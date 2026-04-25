use air::AlphaPowers;
use fiat_shamir::*;
use field::ExtensionField;
use field::PrimeCharacteristicRing;
use poly::*;

use crate::*;

#[allow(clippy::too_many_arguments)]
pub fn sumcheck_prove<'a, EF, SC, M: Into<MleGroup<'a, EF>>>(
    multilinears_f: M,
    computation: &SC,
    extra_data: &SC::ExtraData,
    eq_factor: Option<Vec<EF>>,
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
        None,
        computation,
        extra_data,
        eq_factor,
        prover_state,
        sum,
        store_intermediate_foldings,
    )
}

#[allow(clippy::too_many_arguments)]
pub fn sumcheck_fold_and_prove<'a, EF, SC, M: Into<MleGroup<'a, EF>>>(
    multilinears_f: M,
    prev_folding_factor: Option<EF>,
    computation: &SC,
    extra_data: &SC::ExtraData,
    eq_factor: Option<Vec<EF>>,
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
    let mut n_rounds = multilinears_f.by_ref().n_vars();
    if prev_folding_factor.is_some() {
        n_rounds -= 1;
    }
    let (challenges, final_folds_f, final_sum) = sumcheck_prove_many_rounds(
        multilinears_f,
        prev_folding_factor,
        computation,
        extra_data,
        eq_factor,
        prover_state,
        sum,
        None,
        n_rounds,
        store_intermediate_foldings,
        0,
    );

    let final_folds_f = final_folds_f.by_ref().unpack().as_owned_or_clone();
    let final_folds = final_folds_f
        .as_extension()
        .unwrap()
        .iter()
        .map(|m| {
            assert_eq!(m.len(), 1);
            m[0]
        })
        .collect::<Vec<_>>();

    (challenges, final_folds, final_sum)
}

#[allow(clippy::too_many_arguments)]
pub fn sumcheck_prove_many_rounds<'a, EF, SC, M: Into<MleGroup<'a, EF>>>(
    multilinears_f: M,
    mut prev_folding_factor: Option<EF>,
    computation: &SC,
    extra_data: &SC::ExtraData,
    mut eq_factor: Option<Vec<EF>>,
    prover_state: &mut impl FSProver<EF>,
    mut sum: EF,
    mut missing_mul_factors: Option<EF>,
    n_rounds: usize,
    store_intermediate_foldings: bool,
    pow_bits: usize,
) -> (MultilinearPoint<EF>, MleGroupOwned<EF>, EF)
where
    EF: ExtensionField<PF<EF>>,
    SC: SumcheckComputation<EF> + 'static,
    SC::ExtraData: AlphaPowers<EF>,
{
    let mut multilinears: MleGroup<'a, EF> = multilinears_f.into();
    let mut n_vars = multilinears.by_ref().n_vars();
    if prev_folding_factor.is_some() {
        n_vars -= 1;
    }

    let mut eq_factor_and_split: Option<(Vec<EF>, SplitEq<EF>)> = eq_factor.take().map(|eq_point| {
        assert_eq!(eq_point.len(), n_vars);
        let split_eq = SplitEq::new(&eq_point[1..]);
        (eq_point, split_eq)
    });

    let mut challenges = Vec::new();
    for _ in 0..n_rounds {
        multilinears.unpack_if_needed();

        let ps = compute_and_send_polynomial(
            &mut multilinears,
            prev_folding_factor,
            computation,
            &eq_factor_and_split,
            extra_data,
            prover_state,
            sum,
            missing_mul_factors,
        );
        prover_state.pow_grinding(pow_bits);
        let challenge = prover_state.sample();
        challenges.push(challenge);

        prev_folding_factor = on_challenge_received(
            &mut multilinears,
            &mut n_vars,
            &mut eq_factor_and_split,
            &mut sum,
            &mut missing_mul_factors,
            challenge,
            &ps,
            store_intermediate_foldings,
        );
    }

    if let Some(pf) = prev_folding_factor {
        multilinears = multilinears.by_ref().fold(pf).into();
    }

    (MultilinearPoint(challenges), multilinears.as_owned().unwrap(), sum)
}

#[allow(clippy::too_many_arguments)]
/// Compute the round polynomial (bare, i.e. without the eq linear factor)
/// without sending it.  `multilinears` is folded-in-place if a
/// `prev_folding_factor` is provided.
pub fn compute_round_polynomial<'a, EF, SC>(
    multilinears: &mut MleGroup<'a, EF>,
    prev_folding_factor: Option<EF>,
    computation: &SC,
    eq_factor_and_split: &Option<(Vec<EF>, SplitEq<EF>)>,
    extra_data: &SC::ExtraData,
    sum: EF,
    missing_mul_factor: Option<EF>,
) -> DensePolynomial<EF>
where
    EF: ExtensionField<PF<EF>>,
    SC: SumcheckComputation<EF> + 'static,
    SC::ExtraData: AlphaPowers<EF>,
{
    // Interpolation points = 0, 2, 3, 4, ...
    // evaluation at 1 is deduced since we know f(0) + f(1) = sum

    let mut p_evals = Vec::<EF>::new();
    let computation_degree = computation.degree();

    let sc_params = SumcheckComputeParams {
        split_eq: eq_factor_and_split.as_ref().map(|(_, split_eq)| split_eq),
        computation,
        extra_data,
        missing_mul_factor,
        sum,
    };
    p_evals.extend(match prev_folding_factor {
        Some(prev_folding_factor) => {
            let (computed_p_evals, folded_multilinears) = fold_and_sumcheck_compute(
                prev_folding_factor,
                &multilinears.by_ref(),
                sc_params,
                computation_degree,
            );
            *multilinears = folded_multilinears.into();
            computed_p_evals
        }
        None => sumcheck_compute(&multilinears.by_ref(), sc_params, computation_degree),
    });

    let p_at_1 = if let Some((eq_factor, _)) = eq_factor_and_split {
        (sum - (EF::ONE - eq_factor[0]) * p_evals[0]) / eq_factor[0]
    } else {
        sum - p_evals[0]
    };
    p_evals.insert(1, p_at_1);

    DensePolynomial::lagrange_interpolation(
        &p_evals
            .iter()
            .enumerate()
            .map(|(i, &val)| (PF::<EF>::from_usize(i), val))
            .collect::<Vec<_>>(),
    )
    .unwrap()
}

#[allow(clippy::too_many_arguments)]
fn compute_and_send_polynomial<'a, EF, SC>(
    multilinears: &mut MleGroup<'a, EF>,
    prev_folding_factor: Option<EF>,
    computation: &SC,
    eq_factor_and_split: &Option<(Vec<EF>, SplitEq<EF>)>,
    extra_data: &SC::ExtraData,
    prover_state: &mut impl FSProver<EF>,
    sum: EF,
    missing_mul_factor: Option<EF>,
) -> DensePolynomial<EF>
where
    EF: ExtensionField<PF<EF>>,
    SC: SumcheckComputation<EF> + 'static,
    SC::ExtraData: AlphaPowers<EF>,
{
    let poly = compute_round_polynomial(
        multilinears,
        prev_folding_factor,
        computation,
        eq_factor_and_split,
        extra_data,
        sum,
        missing_mul_factor,
    );
    let eq_alpha = eq_factor_and_split.as_ref().map(|(p, _)| p[0]);
    prover_state.add_sumcheck_polynomial(&poly.coeffs, eq_alpha);
    poly
}

#[allow(clippy::too_many_arguments)]
pub fn on_challenge_received<'a, EF: ExtensionField<PF<EF>>>(
    multilinears: &mut MleGroup<'a, EF>,
    n_vars: &mut usize,
    eq_factor: &mut Option<(Vec<EF>, SplitEq<EF>)>,
    sum: &mut EF,
    missing_mul_factor: &mut Option<EF>,
    challenge: EF,
    p: &DensePolynomial<EF>,
    store_intermediate_foldings: bool,
) -> Option<EF> {
    // p is the bare polynomial (without eq linear factor).
    // Evaluate at challenge and multiply by eq factor if present.
    *sum = p.evaluate(challenge);
    *n_vars -= 1;

    if let Some((eq_factor, split_eq)) = eq_factor {
        // Multiply sum by eq(α_i, r_i) since the polynomial doesn't include the eq linear factor
        let eq_eval = (EF::ONE - eq_factor[0]) * (EF::ONE - challenge) + eq_factor[0] * challenge;
        *sum *= eq_eval;

        *missing_mul_factor = Some(
            eq_eval * missing_mul_factor.unwrap_or(EF::ONE) / (EF::ONE - eq_factor.get(1).copied().unwrap_or_default()),
        );
        eq_factor.remove(0);
        split_eq.truncate_half();
    }

    if store_intermediate_foldings {
        *multilinears = multilinears.by_ref().fold(challenge).into();
        None
    } else {
        Some(challenge)
    }
}
