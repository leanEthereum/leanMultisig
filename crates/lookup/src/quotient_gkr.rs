/*
Logup* (Lev Soukhanov)

https://eprint.iacr.org/2025/946.pdf

with custom GKR

*/
use multilinear_toolkit::prelude::*;
use p3_field::PackedFieldExtension;
use p3_field::PrimeCharacteristicRing;
use p3_field::{ExtensionField, PrimeField64, dot_product};
use tracing::instrument;
use utils::{FSProver, FSVerifier};

/*
Custom GKR to compute sum of fractions.

A: [a0, a1, a2, a3, a4, a5, a6, a7]
B: [b0, b1, b2, b3, b4, b5, b6, b7]
AB: [a0, a1, a2, a3, a4, a5, a6, a7, b0, b1, b2, b3, b4, b5, b6, b7]
AB' = [a0.b4 + a4.b0, a1.b5 +a5.b1, a2.b6 + a6.b2, a3.b7 + a7.b3, b0.b4, b1.b5, b2.b6, b3.b7] (sum of quotients 2 by 2)

For i = (i1, i2, ..., i_{n-1}) on the hypercube:
AB'(i1, i2, ..., i_{n-1}) = i1.AB(1, 0, i2, i3, ..., i_{n-1}).AB(1, 1, i2, i3, ..., i_{n-1})
                            + (1 - i1).[AB(0, 0, i2, i3, ..., i_{n-1}).AB(1, 1, i2, i3, ..., i_{n-1}) + AB(0, 1, i2, i3, ..., i_{n-1}).AB(1, 0, i2, i3, ..., i_{n-1})]
                          = i1.AB(1 0 --- ).AB(1 1 --- ) + (1 - i1).[AB(0 0 --- ).AB(1 1 --- ) + AB(0 1 --- ).AB(1 0 --- )]
                          = U4.U2.U3 + U5.[U0.U3 + U1.U2]
with: U0 = AB(0 0 --- )
      U1 = AB(0  1 ---)
      U2 = AB(1 0 --- )
      U3 = AB(1 1 --- )
      U4 = i1
      U5 = (1 - i1)

*/

#[instrument(skip_all)]
pub fn prove_gkr_quotient<EF>(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    numerators: &[EFPacking<EF>],
    (c, denominator_indexes): (EF, &[PF<EF>]),
    n_non_zeros_numerator: Option<usize>, // final_layer[n_non_zeros_numerator..n / 2] are zeros
) -> (Evaluation<EF>, EF, EF)
where
    EF: ExtensionField<PF<EF>>,
    PF<EF>: PrimeField64,
{
    let n = (2 * numerators.len() * packing_width::<EF>()).ilog2() as usize;
    let n_non_zeros_numerator = n_non_zeros_numerator.unwrap_or(numerators.len());
    let mut layers_packed = Vec::new();
    let mut layers_not_packed = Vec::new();
    let last_packed = n
        .checked_sub(6 + packing_log_width::<EF>())
        .expect("TODO small GKR, no packing");
    let denominator_indexes_packed = PFPacking::<EF>::pack_slice(denominator_indexes);
    let c_packed = EFPacking::<EF>::from(c);
    layers_packed.push(sum_quotients_2_by_2_num_and_den(
        numerators,
        |i| c_packed - denominator_indexes_packed[i],
        Some(n_non_zeros_numerator),
    ));
    for i in 0..last_packed - 1 {
        layers_packed.push(sum_quotients_2_by_2(&layers_packed[i], None));
    }
    layers_not_packed.push(sum_quotients_2_by_2(
        &unpack_extension(&layers_packed[last_packed - 1]),
        None,
    ));
    for i in 0..n - last_packed - 2 {
        layers_not_packed.push(sum_quotients_2_by_2(&layers_not_packed[i], None));
    }

    assert_eq!(layers_not_packed[n - last_packed - 2].len(), 2);
    prover_state.add_extension_scalars(&layers_not_packed[n - last_packed - 2]);

    let point = MultilinearPoint(vec![prover_state.sample()]);
    let mut claim = Evaluation::new(
        point.clone(),
        layers_not_packed[n - last_packed - 2].evaluate(&point),
    );

    for layer in layers_not_packed.iter().rev().skip(1) {
        (claim, _, _) = prove_gkr_quotient_step(prover_state, layer, &claim);
    }
    for layer in layers_packed.iter().rev() {
        (claim, _, _) = prove_gkr_quotient_step_packed(prover_state, layer, &claim);
    }
    let (up_layer_eval_left, up_layer_eval_right);
    (claim, up_layer_eval_left, up_layer_eval_right) = prove_gkr_quotient_step_packed_first_round(
        prover_state,
        numerators,
        (c_packed, denominator_indexes_packed),
        &claim,
        Some(n_non_zeros_numerator),
    );

    (claim, up_layer_eval_left, up_layer_eval_right)
}

fn prove_gkr_quotient_step<EF>(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    up_layer: &[EF],
    claim: &Evaluation<EF>,
) -> (Evaluation<EF>, EF, EF)
where
    EF: ExtensionField<PF<EF>>,
    PF<EF>: PrimeField64,
{
    assert_eq!(up_layer.len().ilog2() as usize - 1, claim.point.0.len());
    let len = up_layer.len();
    let mid_len = len / 2;
    let quarter_len = mid_len / 2;

    let eq_poly = eval_eq(&claim.point.0[1..]);

    let sum_x = (0..up_layer.len() / 4)
        .into_par_iter()
        .map(|i| {
            let eq_eval = eq_poly[i];
            let u2 = up_layer[mid_len + i];
            let u3 = up_layer[mid_len + quarter_len + i];
            eq_eval * u2 * u3
        })
        .sum::<EF>();

    let sum_one_minus_x = (claim.value - sum_x * claim.point[0]) / (EF::ONE - claim.point[0]);

    let mid_len = up_layer.len() / 2;
    let quarter_len = mid_len / 2;
    let first_sumcheck_polynomial =
        &DensePolynomial::new(vec![
            EF::ONE - claim.point[0],
            claim.point[0].double() - EF::ONE,
        ]) * &DensePolynomial::new(vec![sum_one_minus_x, sum_x - sum_one_minus_x]);

    // sanity check
    assert_eq!(
        first_sumcheck_polynomial.evaluate(EF::ZERO) + first_sumcheck_polynomial.evaluate(EF::ONE),
        claim.value
    );

    prover_state.add_extension_scalars(&first_sumcheck_polynomial.coeffs);

    let first_sumcheck_challenge = prover_state.sample();

    let next_sum = first_sumcheck_polynomial.evaluate(first_sumcheck_challenge);

    let (u0_folded, u1_folded, u2_folded, u3_folded) = (
        &up_layer[..quarter_len],
        &up_layer[quarter_len..mid_len],
        &up_layer[mid_len..mid_len + quarter_len],
        &up_layer[mid_len + quarter_len..],
    );

    let u4_const = first_sumcheck_challenge;
    let u5_const = EF::ONE - first_sumcheck_challenge;
    let missing_mul_factor = first_sumcheck_challenge * claim.point[0]
        + (EF::ONE - first_sumcheck_challenge) * (EF::ONE - claim.point[0]);

    let (sc_point, quarter_evals) = if up_layer.len() == 4 {
        (
            MultilinearPoint(vec![first_sumcheck_challenge]),
            vec![u0_folded[0], u1_folded[0], u2_folded[0], u3_folded[0]],
        )
    } else {
        let (mut sc_point, inner_evals, _) = sumcheck_prove::<EF, _, _, _>(
            1,
            MleGroupRef::Extension(vec![u0_folded, u1_folded, u2_folded, u3_folded]),
            &GKRQuotientComputation { u4_const, u5_const },
            &GKRQuotientComputation { u4_const, u5_const },
            &[],
            Some((claim.point.0[1..].to_vec(), None)),
            false,
            prover_state,
            next_sum,
            Some(missing_mul_factor),
        );
        sc_point.insert(0, first_sumcheck_challenge);
        (sc_point, inner_evals)
    };

    prover_state.add_extension_scalars(&quarter_evals);

    let mixing_challenge_a = prover_state.sample();
    let mixing_challenge_b = prover_state.sample();

    let mut next_point = sc_point;
    next_point.0.insert(0, mixing_challenge_a);
    next_point.0[1] = mixing_challenge_b;

    let up_layer_eval_left =
        quarter_evals[0] * (EF::ONE - mixing_challenge_b) + quarter_evals[1] * mixing_challenge_b;
    let up_layer_eval_right =
        quarter_evals[2] * (EF::ONE - mixing_challenge_b) + quarter_evals[3] * mixing_challenge_b;

    let next_claim = quarter_evals.evaluate(&MultilinearPoint(vec![
        mixing_challenge_a,
        mixing_challenge_b,
    ]));

    (
        Evaluation::new(next_point, next_claim),
        up_layer_eval_left,
        up_layer_eval_right,
    )
}

fn prove_gkr_quotient_step_packed_first_round<EF>(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    numerators: &[EFPacking<EF>],
    (c_packed, denominator_indexes): (EFPacking<EF>, &[PFPacking<EF>]),
    claim: &Evaluation<EF>,
    _n_non_zeros_numerator: Option<usize>, // TODO
) -> (Evaluation<EF>, EF, EF)
where
    EF: ExtensionField<PF<EF>>,
    PF<EF>: PrimeField64,
{
    assert_eq!(
        numerators.len() * packing_width::<EF>(),
        1 << claim.point.0.len()
    );
    assert_eq!(denominator_indexes.len(), numerators.len());

    let mid_len_packed = numerators.len();
    let quarter_len_packed = mid_len_packed / 2;

    let mut eq_poly_packed = eval_eq_packed(&claim.point.0[1..]);

    let numerators_quarters = split_at_many(
        numerators,
        &(1..4).map(|i| i * numerators.len() / 4).collect::<Vec<_>>(),
    );
    let denominators_quarters = split_at_many(
        denominator_indexes,
        &(1..4)
            .map(|i| i * denominator_indexes.len() / 4)
            .collect::<Vec<_>>(),
    );

    let (eq_mle_left, eq_mle_right) = eq_poly_packed.split_at(eq_poly_packed.len() / 2);

    let minus_c_packed = -c_packed;
    let c_packed_square = c_packed.square();

    let (sum_x_packed, c0_term_single, c2_term_single, c0_term_double, c2_term_double) =
        numerators_quarters[0]
            .par_iter()
            .zip(numerators_quarters[1].par_iter())
            .zip(numerators_quarters[2].par_iter())
            .zip(numerators_quarters[3].par_iter())
            .zip(denominators_quarters[0].par_iter())
            .zip(denominators_quarters[1].par_iter())
            .zip(denominators_quarters[2].par_iter())
            .zip(denominators_quarters[3].par_iter())
            .zip(eq_mle_left.par_iter())
            .zip(eq_mle_right.par_iter())
            .map(
                |(
                    (
                        (
                            (
                                (
                                    ((((&u0_left, &u0_right), &u1_left), &u1_right), &u2_left),
                                    &u2_right,
                                ),
                                &u3_left,
                            ),
                            &u3_right,
                        ),
                        &eq_val_left,
                    ),
                    &eq_val_right,
                )| {
                    // let x_sum_left = eq_val_left * u2_left * u3_left;
                    let x_sum_left = eq_val_left
                        * (c_packed_square
                            + minus_c_packed * (u2_left + u3_left)
                            + u2_left * u3_left);
                    let x_sum_right = eq_val_right
                        * (c_packed_square
                            + minus_c_packed * (u2_right + u3_right)
                            + u2_right * u3_right);
                    let x_sum = x_sum_left + x_sum_right;

                    // anticipation for the next sumcheck polynomial
                    let c0_term_single = x_sum_left;
                    let c2_term_single = eq_val_left * (u3_right - u3_left) * (u2_right - u2_left);

                    let c0_term_double_a = u0_left * (c_packed - u3_left);
                    let c2_term_double_a = (u0_right - u0_left) * (u3_left - u3_right);
                    let c0_term_double_b = (c_packed - u2_left) * u1_left;
                    let c2_term_double_b = (u1_right - u1_left) * (u2_left - u2_right);
                    let mut c0_term_double = c0_term_double_a + c0_term_double_b;
                    let mut c2_term_double = c2_term_double_a + c2_term_double_b;
                    c0_term_double *= eq_val_left;
                    c2_term_double *= eq_val_left;

                    (
                        x_sum,
                        c0_term_single,
                        c2_term_single,
                        c0_term_double,
                        c2_term_double,
                    )
                },
            )
            .reduce(
                || {
                    (
                        EFPacking::<EF>::ZERO,
                        EFPacking::<EF>::ZERO,
                        EFPacking::<EF>::ZERO,
                        EFPacking::<EF>::ZERO,
                        EFPacking::<EF>::ZERO,
                    )
                },
                |(x, a0, a1, a2, a3), (y, b0, b1, b2, b3)| {
                    (x + y, a0 + b0, a1 + b1, a2 + b2, a3 + b3)
                },
            );

    let sum_x = EFPacking::<EF>::to_ext_iter([sum_x_packed]).sum::<EF>();
    let sum_one_minus_x = (claim.value - sum_x * claim.point[0]) / (EF::ONE - claim.point[0]);

    let sumcheck_polynomial_1 =
        &DensePolynomial::new(vec![
            EF::ONE - claim.point[0],
            claim.point[0].double() - EF::ONE,
        ]) * &DensePolynomial::new(vec![sum_one_minus_x, sum_x - sum_one_minus_x]);

    // sanity check
    assert_eq!(
        sumcheck_polynomial_1.evaluate(EF::ZERO) + sumcheck_polynomial_1.evaluate(EF::ONE),
        claim.value
    );

    prover_state.add_extension_scalars(&sumcheck_polynomial_1.coeffs);
    let sumcheck_challenge_1 = prover_state.sample();
    let sum_1 = sumcheck_polynomial_1.evaluate(sumcheck_challenge_1);

    let u4_const = sumcheck_challenge_1;
    let u5_const = EF::ONE - sumcheck_challenge_1;
    let mut missing_mul_factor = (sumcheck_challenge_1 * claim.point[0]
        + (EF::ONE - sumcheck_challenge_1) * (EF::ONE - claim.point[0]))
        / (EF::ONE - claim.point[1]);

    let c0 = c0_term_single * u4_const + c0_term_double * u5_const;
    let c2 = c2_term_single * u4_const + c2_term_double * u5_const;

    let c0 = EFPacking::<EF>::to_ext_iter([c0]).sum::<EF>();
    let c2 = EFPacking::<EF>::to_ext_iter([c2]).sum::<EF>();

    let first_eq_factor = claim.point[1];
    let c1 = ((sum_1 / missing_mul_factor) - c2 * first_eq_factor - c0) / first_eq_factor;

    let mut sumcheck_polynomial_2 = DensePolynomial::new(vec![
        c0 * missing_mul_factor,
        c1 * missing_mul_factor,
        c2 * missing_mul_factor,
    ]);

    sumcheck_polynomial_2 *= &DensePolynomial::lagrange_interpolation(&[
        (PF::<EF>::ZERO, EF::ONE - first_eq_factor),
        (PF::<EF>::ONE, first_eq_factor),
    ])
    .unwrap();

    prover_state.add_extension_scalars(&sumcheck_polynomial_2.coeffs);
    let sumcheck_challenge_2 = prover_state.sample();
    let sum_2 = sumcheck_polynomial_2.evaluate(sumcheck_challenge_2);

    eq_poly_packed.resize(eq_poly_packed.len() / 4, Default::default());
    missing_mul_factor *= ((EF::ONE - claim.point[1]) * (EF::ONE - sumcheck_challenge_2)
        + claim.point[1] * sumcheck_challenge_2)
        / (EF::ONE - claim.point.get(2).copied().unwrap_or_default());

    let batching_scalars = [EF::ONE - sumcheck_challenge_2, sumcheck_challenge_2];
    let (u0_folded_packed, u1_folded_packed) = rayon::join(
        || {
            fold_multilinear(
                &numerators[..quarter_len_packed],
                &batching_scalars,
                &|e, f| e * f,
            )
        },
        || {
            fold_multilinear(
                &numerators[quarter_len_packed..],
                &batching_scalars,
                &|e, f| e * f,
            )
        },
    );

    let sumcheck_challenge_2_packed = EFPacking::<EF>::from(sumcheck_challenge_2);

    let u2_folded_packed = denominator_indexes[..quarter_len_packed / 2]
        .par_iter()
        .zip(denominator_indexes[quarter_len_packed / 2..quarter_len_packed].par_iter())
        .map(|(&l, &r)| c_packed - l + sumcheck_challenge_2_packed * (l - r))
        .collect();
    let u3_folded_packed = denominator_indexes[quarter_len_packed..quarter_len_packed * 3 / 2]
        .par_iter()
        .zip(denominator_indexes[quarter_len_packed * 3 / 2..].par_iter())
        .map(|(&l, &r)| c_packed - l + sumcheck_challenge_2_packed * (l - r))
        .collect();

    let (mut sc_point, quarter_evals, _) = sumcheck_fold_and_prove::<EF, _, _, _>(
        1,
        MleGroupOwned::ExtensionPacked(vec![
            u0_folded_packed,
            u1_folded_packed,
            u2_folded_packed,
            u3_folded_packed,
        ]),
        None,
        &GKRQuotientComputation { u4_const, u5_const },
        &GKRQuotientComputation { u4_const, u5_const },
        &[],
        Some((
            claim.point.0[2..].to_vec(),
            Some(MleOwned::ExtensionPacked(eq_poly_packed)),
        )),
        false,
        prover_state,
        sum_2,
        Some(missing_mul_factor),
    );
    sc_point.splice(0..0, [sumcheck_challenge_1, sumcheck_challenge_2]);

    prover_state.add_extension_scalars(&quarter_evals);

    let mixing_challenge_a = prover_state.sample();
    let mixing_challenge_b = prover_state.sample();

    let mut next_point = sc_point.clone();
    next_point.0.insert(0, mixing_challenge_a);
    next_point.0[1] = mixing_challenge_b;

    let up_layer_eval_left =
        quarter_evals[0] * (EF::ONE - mixing_challenge_b) + quarter_evals[1] * mixing_challenge_b;
    let up_layer_eval_right =
        quarter_evals[2] * (EF::ONE - mixing_challenge_b) + quarter_evals[3] * mixing_challenge_b;

    let next_claim = quarter_evals.evaluate(&MultilinearPoint(vec![
        mixing_challenge_a,
        mixing_challenge_b,
    ]));

    (
        Evaluation::new(next_point, next_claim),
        up_layer_eval_left,
        up_layer_eval_right,
    )
}

fn prove_gkr_quotient_step_packed<EF>(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    up_layer_packed: &[EFPacking<EF>],
    claim: &Evaluation<EF>,
) -> (Evaluation<EF>, EF, EF)
where
    EF: ExtensionField<PF<EF>>,
    PF<EF>: PrimeField64,
{
    assert_eq!(
        up_layer_packed.len() * packing_width::<EF>(),
        2 << claim.point.0.len()
    );

    let len_packed = up_layer_packed.len();
    let mid_len_packed = len_packed / 2;
    let quarter_len_packed = mid_len_packed / 2;

    let mut eq_poly_packed = eval_eq_packed(&claim.point.0[1..]);

    let up_layer_octics = split_at_many(
        up_layer_packed,
        &(1..8)
            .map(|i| i * up_layer_packed.len() / 8)
            .collect::<Vec<_>>(),
    );

    let (eq_mle_left, eq_mle_right) = eq_poly_packed.split_at(eq_poly_packed.len() / 2);

    let (sum_x_packed, c0_term_single, c2_term_single, c0_term_double, c2_term_double) =
        up_layer_octics[0]
            .par_iter()
            .zip(up_layer_octics[1].par_iter())
            .zip(up_layer_octics[2].par_iter())
            .zip(up_layer_octics[3].par_iter())
            .zip(up_layer_octics[4].par_iter())
            .zip(up_layer_octics[5].par_iter())
            .zip(up_layer_octics[6].par_iter())
            .zip(up_layer_octics[7].par_iter())
            .zip(eq_mle_left.par_iter())
            .zip(eq_mle_right.par_iter())
            .map(
                |(
                    (
                        (
                            (
                                (
                                    ((((&u0_left, &u0_right), &u1_left), &u1_right), &u2_left),
                                    &u2_right,
                                ),
                                &u3_left,
                            ),
                            &u3_right,
                        ),
                        &eq_val_left,
                    ),
                    &eq_val_right,
                )| {
                    let x_sum_left = eq_val_left * u2_left * u3_left;
                    let x_sum_right = eq_val_right * u2_right * u3_right;
                    let x_sum = x_sum_left + x_sum_right;

                    // anticipation for the next sumcheck polynomial
                    let c0_term_single = x_sum_left;
                    let mut c2_term_single = (u3_right - u3_left) * (u2_right - u2_left);
                    c2_term_single *= eq_val_left;

                    let c0_term_double_a = u0_left * u3_left;
                    let c2_term_double_a = (u0_right - u0_left) * (u3_right - u3_left);
                    let c0_term_double_b = u2_left * u1_left;
                    let c2_term_double_b = (u1_right - u1_left) * (u2_right - u2_left);
                    let mut c0_term_double = c0_term_double_a + c0_term_double_b;
                    let mut c2_term_double = c2_term_double_a + c2_term_double_b;
                    c0_term_double *= eq_val_left;
                    c2_term_double *= eq_val_left;

                    (
                        x_sum,
                        c0_term_single,
                        c2_term_single,
                        c0_term_double,
                        c2_term_double,
                    )
                },
            )
            .reduce(
                || {
                    (
                        EFPacking::<EF>::ZERO,
                        EFPacking::<EF>::ZERO,
                        EFPacking::<EF>::ZERO,
                        EFPacking::<EF>::ZERO,
                        EFPacking::<EF>::ZERO,
                    )
                },
                |(x, a0, a1, a2, a3), (y, b0, b1, b2, b3)| {
                    (x + y, a0 + b0, a1 + b1, a2 + b2, a3 + b3)
                },
            );

    let sum_x = EFPacking::<EF>::to_ext_iter([sum_x_packed]).sum::<EF>();
    let sum_one_minus_x = (claim.value - sum_x * claim.point[0]) / (EF::ONE - claim.point[0]);

    let sumcheck_polynomial_1 =
        &DensePolynomial::new(vec![
            EF::ONE - claim.point[0],
            claim.point[0].double() - EF::ONE,
        ]) * &DensePolynomial::new(vec![sum_one_minus_x, sum_x - sum_one_minus_x]);

    // sanity check
    assert_eq!(
        sumcheck_polynomial_1.evaluate(EF::ZERO) + sumcheck_polynomial_1.evaluate(EF::ONE),
        claim.value
    );

    prover_state.add_extension_scalars(&sumcheck_polynomial_1.coeffs);
    let sumcheck_challenge_1 = prover_state.sample();
    let sum_1 = sumcheck_polynomial_1.evaluate(sumcheck_challenge_1);

    let (u0_folded_packed, u1_folded_packed, u2_folded_packed, u3_folded_packed) = (
        &up_layer_packed[..quarter_len_packed],
        &up_layer_packed[quarter_len_packed..mid_len_packed],
        &up_layer_packed[mid_len_packed..mid_len_packed + quarter_len_packed],
        &up_layer_packed[mid_len_packed + quarter_len_packed..],
    );

    let u4_const = sumcheck_challenge_1;
    let u5_const = EF::ONE - sumcheck_challenge_1;
    let mut missing_mul_factor = (sumcheck_challenge_1 * claim.point[0]
        + (EF::ONE - sumcheck_challenge_1) * (EF::ONE - claim.point[0]))
        / (EF::ONE - claim.point[1]);

    let c0 = c0_term_single * u4_const + c0_term_double * u5_const;
    let c2 = c2_term_single * u4_const + c2_term_double * u5_const;

    let c0 = EFPacking::<EF>::to_ext_iter([c0]).sum::<EF>();
    let c2 = EFPacking::<EF>::to_ext_iter([c2]).sum::<EF>();

    let first_eq_factor = claim.point[1];
    let c1 = ((sum_1 / missing_mul_factor) - c2 * first_eq_factor - c0) / first_eq_factor;

    let mut sumcheck_polynomial_2 = DensePolynomial::new(vec![
        c0 * missing_mul_factor,
        c1 * missing_mul_factor,
        c2 * missing_mul_factor,
    ]);

    sumcheck_polynomial_2 *= &DensePolynomial::lagrange_interpolation(&[
        (PF::<EF>::ZERO, EF::ONE - first_eq_factor),
        (PF::<EF>::ONE, first_eq_factor),
    ])
    .unwrap();

    prover_state.add_extension_scalars(&sumcheck_polynomial_2.coeffs);
    let sumcheck_challenge_2 = prover_state.sample();
    let sum_2 = sumcheck_polynomial_2.evaluate(sumcheck_challenge_2);

    eq_poly_packed.resize(eq_poly_packed.len() / 4, Default::default());
    missing_mul_factor *= ((EF::ONE - claim.point[1]) * (EF::ONE - sumcheck_challenge_2)
        + claim.point[1] * sumcheck_challenge_2)
        / (EF::ONE - claim.point.get(2).copied().unwrap_or_default());

    let (mut sc_point, quarter_evals, _) = sumcheck_fold_and_prove::<EF, _, _, _>(
        1,
        MleGroupRef::ExtensionPacked(vec![
            u0_folded_packed,
            u1_folded_packed,
            u2_folded_packed,
            u3_folded_packed,
        ]),
        Some(vec![EF::ONE - sumcheck_challenge_2, sumcheck_challenge_2]),
        &GKRQuotientComputation { u4_const, u5_const },
        &GKRQuotientComputation { u4_const, u5_const },
        &[],
        Some((
            claim.point.0[2..].to_vec(),
            Some(MleOwned::ExtensionPacked(eq_poly_packed)),
        )),
        false,
        prover_state,
        sum_2,
        Some(missing_mul_factor),
    );
    sc_point.splice(0..0, [sumcheck_challenge_1, sumcheck_challenge_2]);

    prover_state.add_extension_scalars(&quarter_evals);

    let mixing_challenge_a = prover_state.sample();
    let mixing_challenge_b = prover_state.sample();

    let mut next_point = sc_point.clone();
    next_point.0.insert(0, mixing_challenge_a);
    next_point.0[1] = mixing_challenge_b;

    let up_layer_eval_left =
        quarter_evals[0] * (EF::ONE - mixing_challenge_b) + quarter_evals[1] * mixing_challenge_b;
    let up_layer_eval_right =
        quarter_evals[2] * (EF::ONE - mixing_challenge_b) + quarter_evals[3] * mixing_challenge_b;

    let next_claim = quarter_evals.evaluate(&MultilinearPoint(vec![
        mixing_challenge_a,
        mixing_challenge_b,
    ]));

    (
        Evaluation::new(next_point, next_claim),
        up_layer_eval_left,
        up_layer_eval_right,
    )
}

pub fn verify_gkr_quotient<EF>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    n_vars: usize,
) -> Result<(EF, Evaluation<EF>), ProofError>
where
    EF: ExtensionField<PF<EF>>,
    PF<EF>: PrimeField64,
{
    let [a, b] = verifier_state.next_extension_scalars_const()?;
    if b == EF::ZERO {
        return Err(ProofError::InvalidProof);
    }
    let quotient = a / b;

    let point = MultilinearPoint(vec![verifier_state.sample()]);
    let value = [a, b].evaluate(&point);
    let mut claim = Evaluation { point, value };

    for i in 1..n_vars {
        claim = verify_gkr_quotient_step(verifier_state, i, &claim)?;
    }

    Ok((quotient, claim))
}

fn verify_gkr_quotient_step<EF>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    current_layer_log_len: usize,
    claim: &Evaluation<EF>,
) -> Result<Evaluation<EF>, ProofError>
where
    EF: ExtensionField<PF<EF>>,
    PF<EF>: PrimeField64,
{
    let (sc_eval, postponed) = sumcheck_verify_with_custom_degree_at_first_round(
        verifier_state,
        current_layer_log_len,
        2,
        3,
    )
    .map_err(|_| ProofError::InvalidProof)?;

    if sc_eval != claim.value {
        return Err(ProofError::InvalidProof);
    }

    let [q0, q1, q2, q3] = verifier_state.next_extension_scalars_const()?;

    let postponed_target = claim.point.eq_poly_outside(&postponed.point)
        * (postponed.point.0[0] * q2 * q3 + (EF::ONE - postponed.point.0[0]) * (q0 * q3 + q1 * q2));
    if postponed_target != postponed.value {
        return Err(ProofError::InvalidProof);
    }

    let mixing_challenge_a = verifier_state.sample();
    let mixing_challenge_b = verifier_state.sample();

    let mut next_point = postponed.point;
    next_point.0.insert(0, mixing_challenge_a);
    next_point.0[1] = mixing_challenge_b;

    let next_claim = dot_product::<EF, _, _>(
        [q0, q1, q2, q3].into_iter(),
        eval_eq(&[mixing_challenge_a, mixing_challenge_b])
            .iter()
            .copied(),
    );

    Ok(Evaluation::new(next_point, next_claim))
}

fn sum_quotients_2_by_2<F: PrimeCharacteristicRing + Sync + Send + Copy>(
    layer: &[F],
    n_non_zeros_numerator: Option<usize>,
) -> Vec<F> {
    let n = layer.len();
    let denominators = &layer[n / 2..];
    sum_quotients_2_by_2_num_and_den(&layer[..n / 2], |i| denominators[i], n_non_zeros_numerator)
}

fn sum_quotients_2_by_2_num_and_den<F: PrimeCharacteristicRing + Sync + Send + Copy>(
    numerators: &[F],
    denominators: impl Fn(usize) -> F + Sync + Send,
    // TODO OPTI: add a mul den x den closure
    n_non_zeros_numerator: Option<usize>,
) -> Vec<F> {
    let n = numerators.len();
    let mut res = unsafe { uninitialized_vec(n) };
    let n_non_zeros_numerator = n_non_zeros_numerator.unwrap_or(n);
    assert!(n_non_zeros_numerator >= n / 2);
    let n_over_2 = n / 2;

    let (new_numerators, new_denominators) = res.split_at_mut(n / 2);
    new_numerators[..n_non_zeros_numerator - n / 2]
        .par_iter_mut()
        .zip(new_denominators[..n_non_zeros_numerator - n / 2].par_iter_mut())
        .enumerate()
        .for_each(|(i, (num, den))| {
            let prev_num_1 = numerators[i];
            let prev_num_2 = numerators[n_over_2 + i];
            let prev_den_1 = denominators(i);
            let prev_den_2 = denominators(n_over_2 + i);
            *num = prev_num_1 * prev_den_2 + prev_num_2 * prev_den_1;
            *den = prev_den_1 * prev_den_2;
        });
    new_numerators[n_non_zeros_numerator - n / 2..]
        .par_iter_mut()
        .zip(new_denominators[n_non_zeros_numerator - n / 2..].par_iter_mut())
        .enumerate()
        .for_each(|(i, (num, den))| {
            let idx = i + n_non_zeros_numerator - n / 2;
            let prev_num_1 = numerators[idx];
            let prev_den_1 = denominators(idx);
            let prev_den_2 = denominators(n_over_2 + idx);
            *num = prev_num_1 * prev_den_2;
            *den = prev_den_1 * prev_den_2;
        });
    res
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_koala_bear::QuinticExtensionFieldKB;
    use rand::{Rng, SeedableRng, rngs::StdRng};
    use std::time::Instant;
    use utils::{build_prover_state, build_verifier_state};

    type EF = QuinticExtensionFieldKB;

    fn sum_all_quotients(nums: &[EF], den: &[EF]) -> EF {
        nums.iter().zip(den.iter()).map(|(&n, &d)| n / d).sum()
    }

    #[test]
    fn test_gkr_quotient_step() {
        let log_n = 12;
        let n = 1 << log_n;

        let mut rng = StdRng::seed_from_u64(0);

        let big = (0..n).map(|_| rng.random()).collect::<Vec<EF>>();
        let small = sum_quotients_2_by_2(&big, None);

        // sanity check
        assert_eq!(
            (0..n / 2).map(|i| big[i] / big[n / 2 + i]).sum::<EF>(),
            (0..n / 4).map(|i| small[i] / small[n / 4 + i]).sum::<EF>()
        );

        let point = MultilinearPoint((0..log_n - 1).map(|_| rng.random()).collect::<Vec<EF>>());
        let eval = small.evaluate(&point);

        let mut prover_state = build_prover_state();

        let time = Instant::now();
        let claim = Evaluation { point, value: eval };
        let _ = prove_gkr_quotient_step_packed(&mut prover_state, &pack_extension(&big), &claim);
        dbg!(time.elapsed());

        let mut verifier_state = build_verifier_state(&prover_state);

        let postponed = verify_gkr_quotient_step(&mut verifier_state, log_n - 1, &claim).unwrap();
        assert_eq!(big.evaluate(&postponed.point), postponed.value);
    }

    #[test]
    fn test_gkr_quotient() {
        let log_n = 10;
        let n = 1 << log_n;

        let mut rng = StdRng::seed_from_u64(0);

        let numerators = (0..n).map(|_| rng.random()).collect::<Vec<EF>>();
        let c: EF = rng.random();
        let denominators_indexes = (0..n)
            .map(|_| PF::<EF>::from_usize(rng.random_range(..n)))
            .collect::<Vec<_>>();
        let denominators = denominators_indexes
            .iter()
            .map(|&i| c - i)
            .collect::<Vec<EF>>();
        let layer = [numerators.clone(), denominators.clone()].concat();
        let real_quotient = sum_all_quotients(&numerators, &denominators);
        let mut prover_state = build_prover_state();

        let _ = prove_gkr_quotient(
            &mut prover_state,
            &pack_extension(&numerators),
            (c, &denominators_indexes),
            None,
        );

        let mut verifier_state = build_verifier_state(&prover_state);

        let (retrieved_quotient, postponed) =
            verify_gkr_quotient::<EF>(&mut verifier_state, 1 + log_n).unwrap();
        assert_eq!(layer.evaluate(&postponed.point), postponed.value);
        assert_eq!(retrieved_quotient, real_quotient);
    }
}
