use p3_air::BaseAir;
use p3_field::{ExtensionField, cyclic_subgroup_known_order, dot_product};
use p3_util::log2_ceil_usize;
use sumcheck::SumcheckComputation;
use utils::univariate_selectors;
use utils::{FSVerifier, PF};
use whir_p3::fiat_shamir::FSChallenger;
use whir_p3::poly::evals::eval_eq;
use whir_p3::poly::multilinear::Evaluation;
use whir_p3::{
    fiat_shamir::errors::ProofError,
    poly::{evals::EvaluationsList, multilinear::MultilinearPoint},
};

use crate::utils::{matrix_down_lde, matrix_up_lde};
use crate::{NormalAir, PackedAir};

use super::table::AirTable;

fn verify_air<EF: ExtensionField<PF<EF>>, A: NormalAir<EF>, AP: PackedAir<EF>>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    table: &AirTable<EF, A, AP>,
    univariate_skips: usize,
    log_n_rows: usize,
) -> Result<(MultilinearPoint<EF>, Vec<EF>), ProofError> {
    let constraints_batching_scalar = verifier_state.sample();

    let n_zerocheck_challenges = log_n_rows + 1 - univariate_skips;
    let global_zerocheck_challenges = verifier_state.sample_vec(n_zerocheck_challenges);

    let (sc_sum, outer_statement) = sumcheck::verify_with_univariate_skip::<EF>(
        verifier_state,
        <A as BaseAir<PF<EF>>>::degree(&table.air) + 1,
        log_n_rows,
        univariate_skips,
    )?;
    if sc_sum != EF::ZERO {
        return Err(ProofError::InvalidProof);
    }

    let outer_selector_evals = univariate_selectors::<PF<EF>>(univariate_skips)
        .iter()
        .map(|s| s.evaluate(outer_statement.point[0]))
        .collect::<Vec<_>>();

    let inner_sums = verifier_state.next_extension_scalars_vec(
        if <A as BaseAir<PF<EF>>>::structured(&table.air) {
            2 * table.n_columns()
        } else {
            table.n_columns()
        },
    )?;

    let zerocheck_selector_evals = univariate_selectors::<PF<EF>>(univariate_skips)
        .iter()
        .map(|s| s.evaluate(global_zerocheck_challenges[0]))
        .collect::<Vec<_>>();

    let constraint_evals = SumcheckComputation::eval(
        &table.air,
        &inner_sums,
        &cyclic_subgroup_known_order(constraints_batching_scalar, table.n_constraints)
            .collect::<Vec<_>>(),
    );

    if dot_product::<EF, _, _>(
        zerocheck_selector_evals.clone().into_iter(),
        outer_selector_evals.iter().copied(),
    ) * MultilinearPoint(
        global_zerocheck_challenges[1..log_n_rows + 1 - univariate_skips].to_vec(),
    )
    .eq_poly_outside(&MultilinearPoint(
        outer_statement.point[1..log_n_rows - univariate_skips + 1].to_vec(),
    )) * constraint_evals
        != outer_statement.value
    {
        return Err(ProofError::InvalidProof);
    }
    let structured_air = <A as BaseAir<PF<EF>>>::structured(&table.air);

    if structured_air {
        verify_structured_columns(
            verifier_state,
            table.n_columns(),
            univariate_skips,
            &inner_sums,
            &Evaluation::new(
                outer_statement.point[1..log_n_rows - univariate_skips + 1].to_vec(),
                outer_statement.value,
            ),
            &outer_selector_evals,
            log_n_rows,
        )
    } else {
        verify_unstructured_columns(
            verifier_state,
            univariate_skips,
            inner_sums,
            &outer_statement.point,
            &outer_selector_evals,
            log_n_rows,
        )
    }
}

impl<EF: ExtensionField<PF<EF>>, A: NormalAir<EF>, AP: PackedAir<EF>> AirTable<EF, A, AP> {
    pub fn verify(
        &self,
        verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
        univariate_skips: usize,
        log_n_rows: usize,
    ) -> Result<(MultilinearPoint<EF>, Vec<EF>), ProofError> {
        verify_air::<EF, A, AP>(verifier_state, self, univariate_skips, log_n_rows)
    }
}

fn verify_unstructured_columns<EF: ExtensionField<PF<EF>>>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    univariate_skips: usize,
    inner_sums: Vec<EF>,
    outer_sumcheck_point: &MultilinearPoint<EF>,
    outer_selector_evals: &[EF],
    log_n_rows: usize,
) -> Result<(MultilinearPoint<EF>, Vec<EF>), ProofError> {
    let n_columns = inner_sums.len();
    let columns_batching_scalars = verifier_state.sample_vec(log2_ceil_usize(n_columns));

    let sub_evals = verifier_state.next_extension_scalars_vec(1 << univariate_skips)?;

    if dot_product::<EF, _, _>(
        sub_evals.iter().copied(),
        outer_selector_evals.iter().copied(),
    ) != dot_product::<EF, _, _>(
        inner_sums.iter().copied(),
        eval_eq(&columns_batching_scalars).iter().copied(),
    ) {
        return Err(ProofError::InvalidProof);
    }

    let epsilons = MultilinearPoint(verifier_state.sample_vec(univariate_skips));
    let common_point = MultilinearPoint(
        [
            epsilons.0.clone(),
            outer_sumcheck_point[1..log_n_rows - univariate_skips + 1].to_vec(),
        ]
        .concat(),
    );

    let evaluations_remaining_to_verify = verifier_state.next_extension_scalars_vec(n_columns)?;

    if sub_evals.evaluate(&epsilons)
        != dot_product(
            eval_eq(&columns_batching_scalars).into_iter(),
            evaluations_remaining_to_verify.iter().copied(),
        )
    {
        return Err(ProofError::InvalidProof);
    }

    Ok((common_point, evaluations_remaining_to_verify))
}

#[allow(clippy::too_many_arguments)] // TODO
fn verify_structured_columns<EF: ExtensionField<PF<EF>>>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    n_columns: usize,
    univariate_skips: usize,
    all_inner_sums: &[EF],
    outer_sumcheck_challenge: &Evaluation<EF>,
    outer_selector_evals: &[EF],
    log_n_rows: usize,
) -> Result<(MultilinearPoint<EF>, Vec<EF>), ProofError> {
    let columns_batching_scalars = verifier_state.sample_vec(log2_ceil_usize(n_columns));
    let alpha = verifier_state.sample();

    let poly_eq_batching_scalars = eval_eq(&columns_batching_scalars);

    let all_witness_up = &all_inner_sums[..n_columns];
    let all_witness_down = &all_inner_sums[n_columns..];

    let sub_evals = verifier_state.next_extension_scalars_vec(1 << univariate_skips)?;

    if dot_product::<EF, _, _>(
        sub_evals.iter().copied(),
        outer_selector_evals.iter().copied(),
    ) != dot_product::<EF, _, _>(
        all_witness_up.iter().copied(),
        poly_eq_batching_scalars.iter().copied(),
    ) + dot_product::<EF, _, _>(
        all_witness_down.iter().copied(),
        poly_eq_batching_scalars.iter().copied(),
    ) * alpha
    {
        return Err(ProofError::InvalidProof);
    }

    let epsilons = MultilinearPoint(verifier_state.sample_vec(univariate_skips));

    let (inner_sum, inner_sumcheck_stement) = sumcheck::verify(verifier_state, log_n_rows, 2)?;

    if inner_sum != sub_evals.evaluate(&epsilons) {
        return Err(ProofError::InvalidProof);
    }

    let matrix_lde_point = [
        epsilons.0,
        outer_sumcheck_challenge.point.to_vec(),
        inner_sumcheck_stement.point.0.clone(),
    ]
    .concat();
    let up = matrix_up_lde(&matrix_lde_point);
    let down = matrix_down_lde(&matrix_lde_point);

    let final_value = inner_sumcheck_stement.value / (up + alpha * down);

    let evaluations_remaining_to_verify = verifier_state.next_extension_scalars_vec(n_columns)?;

    if final_value
        != dot_product(
            eval_eq(&columns_batching_scalars).into_iter(),
            evaluations_remaining_to_verify.iter().copied(),
        )
    {
        return Err(ProofError::InvalidProof);
    }
    Ok((
        inner_sumcheck_stement.point.clone(),
        evaluations_remaining_to_verify,
    ))
}
