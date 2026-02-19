use air::AlphaPowers;
use fiat_shamir::*;
use field::ExtensionField;
use field::PrimeCharacteristicRing;
use poly::*;

use crate::*;

#[allow(clippy::too_many_arguments)]
pub fn sumcheck_prove<'a, EF, SC, M: Into<MleGroup<'a, EF>>>(
    multilinears_f: M,
    multilinears_ef: Option<M>,
    computation: &SC,
    extra_data: &SC::ExtraData,
    eq_factor: Option<(Vec<EF>, Option<MleOwned<EF>>)>, // (a, b, c ...), eq_poly(b, c, ...)
    is_zerofier: bool,
    prover_state: &mut impl FSProver<EF>,
    sum: EF,
    store_intermediate_foldings: bool,
) -> (MultilinearPoint<EF>, Vec<EF>, EF)
where
    EF: ExtensionField<PF<EF>>,
    SC: SumcheckComputation<EF> + 'static,
    SC::ExtraData: AlphaPowers<EF>,
{
    sumcheck_fold_and_prove(
        multilinears_f,
        multilinears_ef,
        None,
        computation,
        extra_data,
        eq_factor,
        is_zerofier,
        prover_state,
        sum,
        store_intermediate_foldings,
    )
}

#[allow(clippy::too_many_arguments)]
pub fn sumcheck_fold_and_prove<'a, EF, SC, M: Into<MleGroup<'a, EF>>>(
    multilinears_f: M,
    multilinears_ef: Option<M>,
    prev_folding_factor: Option<EF>,
    computation: &SC,
    extra_data: &SC::ExtraData,
    eq_factor: Option<(Vec<EF>, Option<MleOwned<EF>>)>, // (a, b, c ...), eq_poly(b, c, ...)
    is_zerofier: bool,
    prover_state: &mut impl FSProver<EF>,
    sum: EF,
    store_intermediate_foldings: bool,
) -> (MultilinearPoint<EF>, Vec<EF>, EF)
where
    EF: ExtensionField<PF<EF>>,
    SC: SumcheckComputation<EF> + 'static,
    SC::ExtraData: AlphaPowers<EF>,
{
    let multilinears_f: MleGroup<'a, EF> = multilinears_f.into();
    let multilinears_ef: MleGroup<'a, EF> = match multilinears_ef {
        Some(m) => m.into(),
        None => MleGroupOwned::empty(true, multilinears_f.is_packed()).into(),
    };
    let mut n_rounds = multilinears_f.by_ref().n_vars();
    if prev_folding_factor.is_some() {
        n_rounds -= 1;
    }
    let (challenges, final_folds_f, final_folds_ef, final_sum) = sumcheck_prove_many_rounds(
        multilinears_f,
        Some(multilinears_ef),
        prev_folding_factor,
        computation,
        extra_data,
        eq_factor,
        is_zerofier,
        prover_state,
        sum,
        None,
        n_rounds,
        store_intermediate_foldings,
        0,
    );

    let final_folds = [final_folds_f, final_folds_ef]
        .into_iter()
        .flat_map(|mle| {
            mle.by_ref()
                .as_extension()
                .unwrap()
                .iter()
                .map(|m| {
                    assert_eq!(m.len(), 1);
                    m[0]
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();

    (challenges, final_folds, final_sum)
}

#[allow(clippy::too_many_arguments)]
pub fn sumcheck_prove_many_rounds<'a, EF, SC, M: Into<MleGroup<'a, EF>>>(
    multilinears_f: M,
    multilinears_ef: Option<M>,
    mut prev_folding_factor: Option<EF>,
    computation: &SC,
    extra_data: &SC::ExtraData,
    mut eq_factor: Option<(Vec<EF>, Option<MleOwned<EF>>)>, // (a, b, c ...), eq_poly(b, c, ...)
    mut is_zerofier: bool,
    prover_state: &mut impl FSProver<EF>,
    mut sum: EF,
    mut missing_mul_factors: Option<EF>,
    n_rounds: usize,
    store_intermediate_foldings: bool,
    pow_bits: usize,
) -> (MultilinearPoint<EF>, MleGroupOwned<EF>, MleGroupOwned<EF>, EF)
where
    EF: ExtensionField<PF<EF>>,
    SC: SumcheckComputation<EF> + 'static,
    SC::ExtraData: AlphaPowers<EF>,
{
    let mut multilinears_f: MleGroup<'a, EF> = multilinears_f.into();
    let mut multilinears_ef: MleGroup<'a, EF> = match multilinears_ef {
        Some(m) => m.into(),
        None => MleGroupOwned::empty(true, multilinears_f.is_packed()).into(),
    };
    assert_eq!(multilinears_f.is_packed(), multilinears_ef.is_packed());

    let mut eq_factor: Option<(Vec<EF>, MleOwned<EF>)> = eq_factor.take().map(|(eq_point, eq_mle)| {
        let eq_mle = eq_mle.unwrap_or_else(|| {
            let eval_eq_ext = eval_eq(&eq_point[1..]);
            if multilinears_f.by_ref().is_packed() {
                MleOwned::ExtensionPacked(pack_extension(&eval_eq_ext))
            } else {
                MleOwned::Extension(eval_eq_ext)
            }
        });
        (eq_point, eq_mle)
    });

    let mut n_vars = multilinears_f.by_ref().n_vars();
    if prev_folding_factor.is_some() {
        n_vars -= 1;
    }
    if let Some((eq_point, eq_mle)) = &eq_factor {
        assert_eq!(eq_point.len(), n_vars);
        assert_eq!(eq_mle.by_ref().n_vars(), eq_point.len() - 1);
        if eq_mle.by_ref().is_packed() && !multilinears_f.is_packed() {
            assert!(eq_point.len() < packing_log_width::<EF>());
            multilinears_f = multilinears_f.by_ref().unpack().as_owned_or_clone().into();
            multilinears_ef = multilinears_ef.by_ref().unpack().as_owned_or_clone().into();
        }
    }

    let mut challenges = Vec::new();
    for _ in 0..n_rounds {
        // If Packing is enabled, and there are too little variables, we unpack everything:
        if multilinears_f.by_ref().is_packed() && n_vars <= 1 + packing_log_width::<EF>() {
            // unpack
            multilinears_f = multilinears_f.by_ref().unpack().as_owned_or_clone().into();
            multilinears_ef = multilinears_ef.by_ref().unpack().as_owned_or_clone().into();

            if let Some((_, eq_mle)) = &mut eq_factor {
                *eq_mle = eq_mle.by_ref().unpack().as_owned_or_clone();
            }
        }

        let ps = compute_and_send_polynomial(
            &mut multilinears_f,
            &mut multilinears_ef,
            prev_folding_factor,
            computation,
            &eq_factor,
            extra_data,
            is_zerofier,
            prover_state,
            sum,
            missing_mul_factors,
        );
        prover_state.pow_grinding(pow_bits);
        let challenge = prover_state.sample();
        challenges.push(challenge);

        prev_folding_factor = on_challenge_received(
            &mut multilinears_f,
            &mut multilinears_ef,
            &mut n_vars,
            &mut eq_factor,
            &mut sum,
            &mut missing_mul_factors,
            challenge,
            &ps,
            store_intermediate_foldings,
        );
        is_zerofier = false;
    }

    if let Some(pf) = prev_folding_factor {
        multilinears_f = multilinears_f.by_ref().fold(pf).into();
        multilinears_ef = multilinears_ef.by_ref().fold(pf).into();
    }

    (
        MultilinearPoint(challenges),
        multilinears_f.as_owned().unwrap(),
        multilinears_ef.as_owned().unwrap(),
        sum,
    )
}

#[allow(clippy::too_many_arguments)]
fn compute_and_send_polynomial<'a, EF, SC>(
    multilinears_f: &mut MleGroup<'a, EF>,
    multilinears_ef: &mut MleGroup<'a, EF>,
    prev_folding_factor: Option<EF>,
    computation: &SC,
    eq_factor: &Option<(Vec<EF>, MleOwned<EF>)>, // (a, b, c ...), eq_poly(b, c, ...)
    extra_data: &SC::ExtraData,
    is_zerofier: bool,
    prover_state: &mut impl FSProver<EF>,
    sum: EF,
    missing_mul_factor: Option<EF>,
) -> DensePolynomial<EF>
where
    EF: ExtensionField<PF<EF>>,
    SC: SumcheckComputation<EF> + 'static,
    SC::ExtraData: AlphaPowers<EF>,
{
    let mut p_evals = Vec::<(PF<EF>, EF)>::new();
    let start = if is_zerofier {
        p_evals.extend((0..2).map(|i| (PF::<EF>::from_usize(i), EF::ZERO)));
        2
    } else {
        0
    };

    let computation_degree = computation.degree();
    let zs = (start..=computation_degree).filter(|&i| i != 1).collect::<Vec<_>>();

    let compute_folding_factors: Vec<PF<EF>> = zs.iter().map(|&z| PF::<EF>::from_usize(z)).collect();

    let sc_params = SumcheckComputeParams {
        eq_mle: eq_factor.as_ref().map(|(_, eq_mle)| eq_mle),
        first_eq_factor: eq_factor.as_ref().map(|(first_eq_factor, _)| first_eq_factor[0]),
        folding_factors: &compute_folding_factors,
        computation,
        extra_data,
        missing_mul_factor,
        sum,
    };
    p_evals.extend(match prev_folding_factor {
        Some(prev_folding_factor) => {
            let (computed_p_evals, folded_multilinears_f, folded_multilinears_ef) = fold_and_sumcheck_compute(
                prev_folding_factor,
                &multilinears_f.by_ref(),
                &multilinears_ef.by_ref(),
                sc_params,
                &zs,
            );
            *multilinears_f = folded_multilinears_f.into();
            *multilinears_ef = folded_multilinears_ef.into();
            computed_p_evals
        }
        None => sumcheck_compute(&multilinears_f.by_ref(), &multilinears_ef.by_ref(), sc_params, &zs),
    });

    if !is_zerofier {
        let missing_sum_z = if let Some((eq_factor, _)) = eq_factor {
            (sum - (0..1).map(|i| p_evals[i].1 * (EF::ONE - eq_factor[0])).sum::<EF>()) / eq_factor[0]
        } else {
            sum - p_evals[..1].iter().map(|(_, s)| *s).sum::<EF>()
        };
        p_evals.push((PF::<EF>::from_usize(1), missing_sum_z));
    }

    let mut p = DensePolynomial::lagrange_interpolation(&p_evals).unwrap();

    if let Some((eq_factor, _)) = &eq_factor {
        // https://eprint.iacr.org/2024/108.pdf Section 3.2
        // We do not take advantage of this trick to send less data, but we could do so in the future (TODO)
        p *= &DensePolynomial::lagrange_interpolation(&[
            (PF::<EF>::ZERO, EF::ONE - eq_factor[0]),
            (PF::<EF>::ONE, eq_factor[0]),
        ])
        .unwrap();
    }

    // sanity check
    assert_eq!((0..2).map(|i| p.evaluate(EF::from_usize(i))).sum::<EF>(), sum);

    prover_state.add_extension_scalars(&p.coeffs);

    p
}

#[allow(clippy::too_many_arguments)]
fn on_challenge_received<'a, EF: ExtensionField<PF<EF>>>(
    multilinears_f: &mut MleGroup<'a, EF>,
    multilinears_ef: &mut MleGroup<'a, EF>,
    n_vars: &mut usize,
    eq_factor: &mut Option<(Vec<EF>, MleOwned<EF>)>, // (a, b, c ...), eq_poly(b, c, ...)
    sum: &mut EF,
    missing_mul_factor: &mut Option<EF>,
    challenge: EF,
    p: &DensePolynomial<EF>,
    store_intermediate_foldings: bool,
) -> Option<EF> {
    *sum = p.evaluate(challenge);
    *n_vars -= 1;

    if let Some((eq_factor, eq_mle)) = eq_factor {
        *missing_mul_factor = Some(
            ((EF::ONE - eq_factor[0]) * (EF::ONE - challenge) + eq_factor[0] * challenge)
                * missing_mul_factor.unwrap_or(EF::ONE)
                / (EF::ONE - eq_factor.get(1).copied().unwrap_or_default()),
        );
        eq_factor.remove(0);
        eq_mle.truncate(eq_mle.by_ref().packed_len() / 2);
    }

    if store_intermediate_foldings {
        *multilinears_f = multilinears_f.by_ref().fold(challenge).into();
        *multilinears_ef = multilinears_ef.by_ref().fold(challenge).into();
        None
    } else {
        Some(challenge)
    }
}
