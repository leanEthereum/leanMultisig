/*
Logup* (Lev Soukhanov)

https://eprint.iacr.org/2025/946.pdf

with custom GKR

*/

use p3_field::PackedFieldExtension;
use p3_field::PrimeCharacteristicRing;
use p3_field::{ExtensionField, PrimeField64, dot_product};
use rayon::prelude::*;
use sumcheck::Mle;
use sumcheck::MleGroupRef;
use sumcheck::{SumcheckComputation, SumcheckComputationPacked};
use tracing::instrument;
use utils::pack_extension;
use utils::packing_log_width;
use utils::packing_width;
use utils::unpack_extension;
use utils::{EFPacking, Evaluation, FSProver, FSVerifier, PF, PFPacking};
use whir_p3::fiat_shamir::FSChallenger;
use whir_p3::fiat_shamir::errors::ProofError;
use whir_p3::poly::dense::WhirDensePolynomial;
use whir_p3::poly::evals::EvaluationsList;
use whir_p3::poly::evals::eval_eq;
use whir_p3::poly::multilinear::MultilinearPoint;

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
    final_layer: Vec<EFPacking<EF>>,
) -> (Evaluation<EF>, EF, EF)
where
    EF: ExtensionField<PF<EF>>,
    PF<EF>: PrimeField64,
{
    let n = (final_layer.len() * packing_width::<EF>()).ilog2() as usize;
    let mut layers_packed = Vec::new();
    let mut layers_not_packed = Vec::new();
    let last_packed = n
        .checked_sub(6 + packing_log_width::<EF>())
        .expect("TODO small GKR, no packing");
    layers_packed.push(final_layer);
    for i in 0..last_packed {
        layers_packed.push(sum_quotients_2_by_2(&layers_packed[i]));
    }
    layers_not_packed.push(sum_quotients_2_by_2(&unpack_extension(
        &layers_packed[last_packed],
    )));
    for i in 0..n - last_packed - 2 {
        layers_not_packed.push(sum_quotients_2_by_2(&layers_not_packed[i]));
    }

    assert_eq!(layers_not_packed[n - last_packed - 2].len(), 2);
    prover_state.add_extension_scalars(&layers_not_packed[n - last_packed - 2]);

    let point = MultilinearPoint(vec![prover_state.sample()]);
    let mut claim = Evaluation {
        point: point.clone(),
        value: layers_not_packed[n - last_packed - 2].evaluate(&point),
    };

    let (mut up_layer_eval_left, mut up_layer_eval_right) = (EF::ZERO, EF::ZERO);
    for layer in layers_not_packed.iter().rev().skip(1) {
        (claim, up_layer_eval_left, up_layer_eval_right) =
            prove_gkr_quotient_step(prover_state, layer, &claim);
    }
    for layer in layers_packed.iter().rev() {
        (claim, up_layer_eval_left, up_layer_eval_right) =
            prove_gkr_quotient_step_packed(prover_state, layer, &claim);
    }

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

    let mut sums_x = EF::zero_vec(up_layer.len() / 4);
    let mut sums_one_minus_x = EF::zero_vec(up_layer.len() / 4);

    sums_x
        .par_iter_mut()
        .zip(sums_one_minus_x.par_iter_mut())
        .enumerate()
        .for_each(|(i, (x, one_minus_x))| {
            let eq_eval = eq_poly[i];
            let u0 = up_layer[i];
            let u1 = up_layer[quarter_len + i];
            let u2 = up_layer[mid_len + i];
            let u3 = up_layer[mid_len + quarter_len + i];
            *x = eq_eval * u2 * u3;
            *one_minus_x = eq_eval * (u0 * u3 + u1 * u2);
        });

    let sum_x = sums_x.into_par_iter().sum::<EF>();
    let sum_one_minus_x = sums_one_minus_x.into_par_iter().sum::<EF>();

    let mid_len = up_layer.len() / 2;
    let quarter_len = mid_len / 2;
    let first_sumcheck_polynomial = &WhirDensePolynomial::from_coefficients_vec(vec![
        EF::ONE - claim.point[0],
        claim.point[0].double() - EF::ONE,
    ]) * &WhirDensePolynomial::from_coefficients_vec(vec![
        sum_one_minus_x,
        sum_x - sum_one_minus_x,
    ]);

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
        let (mut sc_point, inner_evals, _) = sumcheck::prove::<EF, _, _, _>(
            1,
            MleGroupRef::Extension(vec![u0_folded, u1_folded, u2_folded, u3_folded]),
            &GKRQuotientComputation { u4_const, u5_const },
            &GKRQuotientComputation { u4_const, u5_const },
            &[EF::ONE],
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
        (next_point, next_claim).into(),
        up_layer_eval_left,
        up_layer_eval_right,
    )
}

fn prove_gkr_quotient_step_packed<EF>(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    up_layer_packed: &Vec<EFPacking<EF>>,
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

    let eq_poly = eval_eq(&claim.point.0[1..]);

    let mut eq_poly_packed = pack_extension(&eq_poly);

    let mut all_sums_x_packed = EFPacking::<EF>::zero_vec(quarter_len_packed);
    let mut all_sums_one_minus_x_packed = EFPacking::<EF>::zero_vec(quarter_len_packed);

    all_sums_x_packed
        .par_iter_mut()
        .zip(all_sums_one_minus_x_packed.par_iter_mut())
        .enumerate()
        .for_each(|(i, (x, one_minus_x))| {
            let eq_eval = eq_poly_packed[i];
            let u0 = up_layer_packed[i];
            let u1 = up_layer_packed[quarter_len_packed + i];
            let u2 = up_layer_packed[mid_len_packed + i];
            let u3 = up_layer_packed[mid_len_packed + quarter_len_packed + i];
            *x = eq_eval * u2 * u3;
            *one_minus_x = eq_eval * (u0 * u3 + u1 * u2);
        });

    let sum_x_packed = all_sums_x_packed.into_par_iter().sum::<EFPacking<EF>>();
    let sum_one_minus_x_packed = all_sums_one_minus_x_packed
        .into_par_iter()
        .sum::<EFPacking<EF>>();

    let sum_x = EFPacking::<EF>::to_ext_iter([sum_x_packed]).sum::<EF>();
    let sum_one_minus_x = EFPacking::<EF>::to_ext_iter([sum_one_minus_x_packed]).sum::<EF>();

    let first_sumcheck_polynomial = &WhirDensePolynomial::from_coefficients_vec(vec![
        EF::ONE - claim.point[0],
        claim.point[0].double() - EF::ONE,
    ]) * &WhirDensePolynomial::from_coefficients_vec(vec![
        sum_one_minus_x,
        sum_x - sum_one_minus_x,
    ]);

    // sanity check
    assert_eq!(
        first_sumcheck_polynomial.evaluate(EF::ZERO) + first_sumcheck_polynomial.evaluate(EF::ONE),
        claim.value
    );

    prover_state.add_extension_scalars(&first_sumcheck_polynomial.coeffs);

    let first_sumcheck_challenge = prover_state.sample();

    let next_sum = first_sumcheck_polynomial.evaluate(first_sumcheck_challenge);

    let (u0_folded_packed, u1_folded_packed, u2_folded_packed, u3_folded_packed) = (
        &up_layer_packed[..quarter_len_packed],
        &up_layer_packed[quarter_len_packed..mid_len_packed],
        &up_layer_packed[mid_len_packed..mid_len_packed + quarter_len_packed],
        &up_layer_packed[mid_len_packed + quarter_len_packed..],
    );

    let u4_const = first_sumcheck_challenge;
    let u5_const = EF::ONE - first_sumcheck_challenge;
    let missing_mul_factor = (first_sumcheck_challenge * claim.point[0]
        + (EF::ONE - first_sumcheck_challenge) * (EF::ONE - claim.point[0]))
        / (EF::ONE - claim.point[1]);

    eq_poly_packed.resize(eq_poly_packed.len() / 2, Default::default());

    let (mut sc_point, quarter_evals, _) = sumcheck::prove::<EF, _, _, _>(
        1,
        MleGroupRef::ExtensionPacked(vec![
            u0_folded_packed,
            u1_folded_packed,
            u2_folded_packed,
            u3_folded_packed,
        ]),
        &GKRQuotientComputation { u4_const, u5_const },
        &GKRQuotientComputation { u4_const, u5_const },
        &[],
        Some((
            claim.point.0[1..].to_vec(),
            Some(Mle::ExtensionPacked(eq_poly_packed)),
        )),
        false,
        prover_state,
        next_sum,
        Some(missing_mul_factor),
    );
    sc_point.insert(0, first_sumcheck_challenge);

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
        (next_point, next_claim).into(),
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
    let (sc_eval, postponed) = sumcheck::verify_with_custom_degree_at_first_round(
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

    Ok((next_point, next_claim).into())
}

pub struct GKRQuotientComputation<EF> {
    u4_const: EF,
    u5_const: EF,
}

impl<IF: ExtensionField<PF<EF>>, EF: ExtensionField<IF>> SumcheckComputation<IF, EF>
    for GKRQuotientComputation<EF>
{
    fn eval(&self, point: &[IF], _: &[EF]) -> EF {
        // U4.U2.U3 + U5.[U0.U3 + U1.U2]
        self.u4_const * point[2] * point[3]
            + self.u5_const * (point[0] * point[3] + point[1] * point[2])
    }
    fn degree(&self) -> usize {
        2
    }
}

impl<EF: ExtensionField<PF<EF>>> SumcheckComputationPacked<EF> for GKRQuotientComputation<EF> {
    fn eval_packed_base(&self, _: &[PFPacking<EF>], _: &[EF]) -> EFPacking<EF> {
        todo!()
    }
    fn eval_packed_extension(&self, point: &[EFPacking<EF>], _: &[EF]) -> EFPacking<EF> {
        point[2] * point[3] * self.u4_const
            + (point[0] * point[3] + point[1] * point[2]) * self.u5_const
    }
    fn degree(&self) -> usize {
        2
    }
}

fn sum_quotients_2_by_2<EF: PrimeCharacteristicRing + Sync + Send + Copy>(layer: &[EF]) -> Vec<EF> {
    let n = layer.len();
    (0..n / 2)
        .into_par_iter()
        .map(|i| {
            if i < n / 4 {
                layer[i] * layer[n * 3 / 4 + i] + layer[n / 4 + i] * layer[n / 2 + i]
            } else {
                layer[n / 4 + i] * layer[n / 2 + i]
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_koala_bear::QuinticExtensionFieldKB;
    use rand::{Rng, SeedableRng, rngs::StdRng};
    use std::time::Instant;
    use utils::{build_prover_state, build_verifier_state};

    type EF = QuinticExtensionFieldKB;

    fn sum_all_quotients(layer: &[EF]) -> EF {
        (0..layer.num_evals() / 2)
            .into_par_iter()
            .map(|i| layer[i] / layer[layer.num_evals() / 2 + i])
            .sum()
    }

    #[test]
    fn test_gkr_quotient_step() {
        let log_n = 21;
        let n = 1 << log_n;

        let mut rng = StdRng::seed_from_u64(0);

        let big = (0..n).map(|_| rng.random()).collect::<Vec<EF>>();
        let small = sum_quotients_2_by_2(&big);

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

        let layer = (0..n).map(|_| rng.random()).collect::<Vec<EF>>();
        let real_quotient = sum_all_quotients(&layer);

        let mut prover_state = build_prover_state();

        let _ = prove_gkr_quotient(&mut prover_state, pack_extension(&layer));

        let mut verifier_state = build_verifier_state(&prover_state);

        let (retrieved_quotient, postponed) =
            verify_gkr_quotient::<EF>(&mut verifier_state, log_n).unwrap();
        assert_eq!(layer.evaluate(&postponed.point), postponed.value);
        assert_eq!(retrieved_quotient, real_quotient);
    }
}
