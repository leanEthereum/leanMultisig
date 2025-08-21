use p3_field::{ExtensionField, cyclic_subgroup_known_order, dot_product};
use p3_util::log2_ceil_usize;
use std::ops::Range;
use sumcheck::SumcheckComputation;
use tracing::instrument;
use utils::univariate_selectors;
use utils::{Evaluation, from_end};
use utils::{FSVerifier, PF};
use whir_p3::fiat_shamir::FSChallenger;
use whir_p3::poly::evals::eval_eq;
use whir_p3::{
    fiat_shamir::errors::ProofError,
    poly::{evals::EvaluationsList, multilinear::MultilinearPoint},
};

use crate::MyAir;
use crate::utils::{matrix_down_lde, matrix_up_lde};

use super::table::AirTable;

#[instrument(name = "air table: verify many", skip_all)]
pub fn verify_many_air_2<'a, EF: ExtensionField<PF<EF>>, A1: MyAir<EF>, A2: MyAir<EF>>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    tables_1: &[&AirTable<EF, A1>],
    tables_2: &[&AirTable<EF, A2>],
    univariate_skips: usize,
    log_lengths: &[usize],
    column_groups: &[Vec<Range<usize>>],
) -> Result<Vec<Vec<Evaluation<EF>>>, ProofError> {
    verify_many_air_3::<EF, A1, A2, A2>(
        verifier_state,
        tables_1,
        tables_2,
        &[],
        univariate_skips,
        log_lengths,
        column_groups,
    )
}

#[instrument(name = "air table: verify many", skip_all)]
pub fn verify_many_air_3<
    'a,
    EF: ExtensionField<PF<EF>>,
    A1: MyAir<EF>,
    A2: MyAir<EF>,
    A3: MyAir<EF>,
>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    tables_1: &[&AirTable<EF, A1>],
    tables_2: &[&AirTable<EF, A2>],
    tables_3: &[&AirTable<EF, A3>],
    univariate_skips: usize,
    log_lengths: &[usize],
    column_groups: &[Vec<Range<usize>>],
) -> Result<Vec<Vec<Evaluation<EF>>>, ProofError> {
    let n_tables = tables_1.len() + tables_2.len() + tables_3.len();
    assert_eq!(n_tables, log_lengths.len());
    let constraints_batching_scalar = verifier_state.sample();

    let max_log_length = *Iterator::max(log_lengths.iter()).unwrap();
    let n_zerocheck_challenges = max_log_length + 1 - univariate_skips;
    let global_zerocheck_challenges = verifier_state.sample_vec(n_zerocheck_challenges);

    let (sc_sum, outer_sumcheck_point, outer_sumcheck_values) =
        sumcheck::verify_with_univariate_skip_in_parallel::<EF>(
            verifier_state,
            univariate_skips,
            &log_lengths,
            &tables_1
                .iter()
                .map(|t| t.air.degree() + 1)
                .chain(tables_2.iter().map(|t| t.air.degree() + 1))
                .chain(tables_3.iter().map(|t| t.air.degree() + 1))
                .collect::<Vec<_>>(),
            true,
        )?;
    if sc_sum.iter().any(|v| *v != EF::ZERO) {
        return Err(ProofError::InvalidProof);
    }

    let outer_selector_evals = univariate_selectors::<PF<EF>>(univariate_skips)
        .iter()
        .map(|s| s.evaluate(outer_sumcheck_point[0]))
        .collect::<Vec<_>>();

    let mut all_inner_sums = vec![];
    for table in tables_1 {
        let inner_sums = verifier_state.next_extension_scalars_vec(if table.air.structured() {
            2 * table.n_columns()
        } else {
            table.n_columns()
        })?;
        all_inner_sums.push(inner_sums);
    }
    for table in tables_2 {
        let inner_sums = verifier_state.next_extension_scalars_vec(if table.air.structured() {
            2 * table.n_columns()
        } else {
            table.n_columns()
        })?;
        all_inner_sums.push(inner_sums);
    }
    for table in tables_3 {
        let inner_sums = verifier_state.next_extension_scalars_vec(if table.air.structured() {
            2 * table.n_columns()
        } else {
            table.n_columns()
        })?;
        all_inner_sums.push(inner_sums);
    }

    let zerocheck_selector_evals = univariate_selectors::<PF<EF>>(univariate_skips)
        .iter()
        .map(|s| s.evaluate(global_zerocheck_challenges[0]))
        .collect::<Vec<_>>();

    let mut global_constraint_evals = vec![];
    {
        let mut i = 0;
        for table in tables_1 {
            global_constraint_evals.push(SumcheckComputation::eval(
                &table.air,
                &all_inner_sums[i],
                &cyclic_subgroup_known_order(constraints_batching_scalar, table.n_constraints)
                    .collect::<Vec<_>>(),
            ));
            i += 1;
        }
        for table in tables_2 {
            global_constraint_evals.push(SumcheckComputation::eval(
                &table.air,
                &all_inner_sums[i],
                &cyclic_subgroup_known_order(constraints_batching_scalar, table.n_constraints)
                    .collect::<Vec<_>>(),
            ));
            i += 1;
        }
        for table in tables_3 {
            global_constraint_evals.push(SumcheckComputation::eval(
                &table.air,
                &all_inner_sums[i],
                &cyclic_subgroup_known_order(constraints_batching_scalar, table.n_constraints)
                    .collect::<Vec<_>>(),
            ));
            i += 1;
        }
    }

    for i in 0..n_tables {
        if dot_product::<EF, _, _>(
            zerocheck_selector_evals.clone().into_iter(),
            outer_selector_evals.iter().copied(),
        ) * MultilinearPoint(
            global_zerocheck_challenges[1..log_lengths[i] + 1 - univariate_skips].to_vec(),
        )
        .eq_poly_outside(&MultilinearPoint(
            outer_sumcheck_point[1..log_lengths[i] - univariate_skips + 1].to_vec(),
        )) * global_constraint_evals[i]
            != outer_sumcheck_values[i]
        {
            return Err(ProofError::InvalidProof);
        }
    }

    let structured_air = tables_1[0].air.structured();
    assert!(
        tables_1
            .iter()
            .all(|t| t.air.structured() == structured_air)
    );
    assert!(
        tables_2
            .iter()
            .all(|t| t.air.structured() == structured_air)
    );
    assert!(
        tables_3
            .iter()
            .all(|t| t.air.structured() == structured_air)
    );

    if structured_air {
        // TODO inner sumchecks in parallel between tables(not usefull in the current protocol but cleaner, more coherent)
        let mut evaluations_remaining_to_verify = vec![];
        for i in 0..n_tables {
            let n_columns = if i < tables_1.len() {
                tables_1[i].n_columns()
            } else if i < tables_1.len() + tables_2.len() {
                tables_2[i - tables_1.len()].n_columns()
            } else {
                tables_3[i - tables_1.len() - tables_2.len()].n_columns()
            };
            evaluations_remaining_to_verify.push(verify_structured_columns(
                verifier_state,
                n_columns,
                univariate_skips,
                &all_inner_sums[i],
                &column_groups[i],
                &Evaluation {
                    point: MultilinearPoint(
                        outer_sumcheck_point[1..log_lengths[i] - univariate_skips + 1].to_vec(),
                    ),
                    value: outer_sumcheck_values[i],
                },
                &outer_selector_evals,
                log_lengths[i],
            )?);
        }
        Ok(evaluations_remaining_to_verify)
    } else {
        verify_many_unstructured_columns(
            verifier_state,
            univariate_skips,
            all_inner_sums,
            &column_groups,
            &outer_sumcheck_point,
            &outer_selector_evals,
            &log_lengths,
        )
    }
}

impl<EF: ExtensionField<PF<EF>>, A: MyAir<EF>> AirTable<EF, A> {
    #[instrument(name = "air table: verify", skip_all)]
    pub fn verify(
        &self,
        verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
        univariate_skips: usize,
        log_n_rows: usize,
        column_groups: &[Range<usize>],
    ) -> Result<Vec<Evaluation<EF>>, ProofError> {
        Ok(verify_many_air_3::<EF, A, A, A>(
            verifier_state,
            &[self],
            &[],
            &[],
            univariate_skips,
            &[log_n_rows],
            &[column_groups.to_vec()],
        )?
        .pop()
        .unwrap())
    }
}

fn verify_many_unstructured_columns<EF: ExtensionField<PF<EF>>>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    univariate_skips: usize,
    all_inner_sums: Vec<Vec<EF>>,
    column_groups: &[Vec<Range<usize>>],
    outer_sumcheck_point: &MultilinearPoint<EF>,
    outer_selector_evals: &[EF],
    log_lengths: &[usize],
) -> Result<Vec<Vec<Evaluation<EF>>>, ProofError> {
    let max_columns_per_group = Iterator::max(
        column_groups
            .iter()
            .map(|g| Iterator::max(g.iter().map(|r| r.len())).unwrap()),
    )
    .unwrap();
    let log_max_columns_per_group = log2_ceil_usize(max_columns_per_group);
    let columns_batching_scalars = verifier_state.sample_vec(log_max_columns_per_group);

    let mut all_all_sub_evals = vec![];
    for i in 0..column_groups.len() {
        let mut all_sub_evals = vec![];
        for group in &column_groups[i] {
            let sub_evals = verifier_state.next_extension_scalars_vec(1 << univariate_skips)?;

            if dot_product::<EF, _, _>(
                sub_evals.iter().copied(),
                outer_selector_evals.iter().copied(),
            ) != dot_product::<EF, _, _>(
                all_inner_sums[i][group.clone()].iter().copied(),
                eval_eq(&from_end(
                    &columns_batching_scalars,
                    log2_ceil_usize(group.len()),
                ))[..group.len()]
                    .iter()
                    .copied(),
            ) {
                return Err(ProofError::InvalidProof);
            }

            all_sub_evals.push(sub_evals);
        }
        all_all_sub_evals.push(all_sub_evals);
    }

    let epsilons = MultilinearPoint(verifier_state.sample_vec(univariate_skips));

    let mut all_evaluations_remaining_to_verify = vec![];
    for (i, column_groups) in column_groups.iter().enumerate() {
        let mut evaluations_remaining_to_verify = vec![];
        for (j, group) in column_groups.iter().enumerate() {
            let final_value = all_all_sub_evals[i][j].evaluate(&epsilons);
            let final_point = MultilinearPoint(
                [
                    from_end(&columns_batching_scalars, log2_ceil_usize(group.len())).to_vec(),
                    epsilons.0.clone(),
                    outer_sumcheck_point[1..log_lengths[i] - univariate_skips + 1].to_vec(),
                ]
                .concat(),
            );
            evaluations_remaining_to_verify.push(Evaluation {
                point: final_point,
                value: final_value,
            });
        }
        all_evaluations_remaining_to_verify.push(evaluations_remaining_to_verify);
    }

    Ok(all_evaluations_remaining_to_verify)
}

fn verify_structured_columns<EF: ExtensionField<PF<EF>>>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    n_columns: usize,
    univariate_skips: usize,
    all_inner_sums: &[EF],
    column_groups: &[Range<usize>],
    outer_sumcheck_challenge: &Evaluation<EF>,
    outer_selector_evals: &[EF],
    log_n_rows: usize,
) -> Result<Vec<Evaluation<EF>>, ProofError> {
    let max_columns_per_group = Iterator::max(column_groups.iter().map(|g| g.len())).unwrap();
    let log_max_columns_per_group = log2_ceil_usize(max_columns_per_group);
    let columns_batching_scalars = verifier_state.sample_vec(log_max_columns_per_group);

    let alpha = verifier_state.sample();

    let all_witness_up = &all_inner_sums[..n_columns];
    let all_witness_down = &all_inner_sums[n_columns..];
    assert_eq!(all_witness_up.len(), all_witness_down.len());

    let mut all_sub_evals = vec![];
    for group in column_groups {
        let sub_evals = verifier_state.next_extension_scalars_vec(1 << univariate_skips)?;

        let witness_up = &all_witness_up[group.clone()];
        let witness_down = &all_witness_down[group.clone()];

        if dot_product::<EF, _, _>(
            sub_evals.iter().copied(),
            outer_selector_evals.iter().copied(),
        ) != dot_product::<EF, _, _>(
            witness_up.iter().copied(),
            eval_eq(&from_end(
                &columns_batching_scalars,
                log2_ceil_usize(group.len()),
            ))[..group.len()]
                .iter()
                .copied(),
        ) + dot_product::<EF, _, _>(
            witness_down.iter().copied(),
            eval_eq(&from_end(
                &columns_batching_scalars,
                log2_ceil_usize(group.len()),
            ))[..group.len()]
                .iter()
                .copied(),
        ) * alpha
        {
            return Err(ProofError::InvalidProof);
        }

        all_sub_evals.push(sub_evals);
    }

    let epsilons = MultilinearPoint(verifier_state.sample_vec(univariate_skips));

    let (all_batched_inner_sums, inner_sumcheck_challenge_point, inner_sumcheck_challenge_values) =
        sumcheck::verify_in_parallel(
            verifier_state,
            &vec![log_n_rows; column_groups.len()],
            &vec![2; column_groups.len()],
            true,
        )?;

    for (batched_inner_sum, sub_evals) in all_batched_inner_sums.into_iter().zip(all_sub_evals) {
        if batched_inner_sum != sub_evals.evaluate(&epsilons) {
            return Err(ProofError::InvalidProof);
        }
    }

    let mut evaluations_remaining_to_verify = vec![];
    for (group, inner_sumcheck_challenge_value) in
        column_groups.iter().zip(inner_sumcheck_challenge_values)
    {
        let matrix_lde_point = [
            epsilons.0.clone(),
            outer_sumcheck_challenge.point.to_vec(),
            inner_sumcheck_challenge_point.0.clone(),
        ]
        .concat();
        let up = matrix_up_lde(&matrix_lde_point);
        let down = matrix_down_lde(&matrix_lde_point);

        let final_value = inner_sumcheck_challenge_value / (up + alpha * down);

        let final_point = [
            from_end(&columns_batching_scalars, log2_ceil_usize(group.len())).to_vec(),
            inner_sumcheck_challenge_point.0.clone(),
        ]
        .concat();

        evaluations_remaining_to_verify.push(Evaluation {
            point: MultilinearPoint(final_point),
            value: final_value,
        });
    }
    Ok(evaluations_remaining_to_verify)
}
