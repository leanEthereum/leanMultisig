use p3_air::BaseAir;
use p3_field::{ExtensionField, cyclic_subgroup_known_order, dot_product};
use p3_util::log2_ceil_usize;
use std::ops::Range;
use sumcheck::SumcheckComputation;
use utils::from_end;
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
    log_length: usize,
    column_groups: &[Range<usize>],
) -> Result<Vec<Evaluation<EF>>, ProofError> {
    let constraints_batching_scalar = verifier_state.sample();

    let n_zerocheck_challenges = log_length + 1 - univariate_skips;
    let global_zerocheck_challenges = verifier_state.sample_vec(n_zerocheck_challenges);

    let (sc_sum, outer_statement) = sumcheck::verify_with_univariate_skip::<EF>(
        verifier_state,
        <A as BaseAir<PF<EF>>>::degree(&table.air) + 1,
        log_length,
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
        global_zerocheck_challenges[1..log_length + 1 - univariate_skips].to_vec(),
    )
    .eq_poly_outside(&MultilinearPoint(
        outer_statement.point[1..log_length - univariate_skips + 1].to_vec(),
    )) * constraint_evals
        != outer_statement.value
    {
        return Err(ProofError::InvalidProof);
    }
    let structured_air = <A as BaseAir<PF<EF>>>::structured(&table.air);

    if structured_air {
        verify_structured_columns(
            verifier_state,
            StructuredColumnsArgs {
                n_columns: table.n_columns(),
                univariate_skips,
                all_inner_sums: &inner_sums,
                column_groups,
                outer_sumcheck_challenge: &Evaluation::new(
                    outer_statement.point[1..log_length - univariate_skips + 1].to_vec(),
                    outer_statement.value,
                ),
                outer_selector_evals: &outer_selector_evals,
                log_n_rows: log_length,
            },
        )
    } else {
        verify_many_unstructured_columns(
            verifier_state,
            univariate_skips,
            inner_sums,
            column_groups,
            &outer_statement.point,
            &outer_selector_evals,
            log_length,
        )
    }
}

impl<EF: ExtensionField<PF<EF>>, A: NormalAir<EF>, AP: PackedAir<EF>> AirTable<EF, A, AP> {
    pub fn verify(
        &self,
        verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
        univariate_skips: usize,
        log_n_rows: usize,
        column_groups: &[Range<usize>],
    ) -> Result<Vec<Evaluation<EF>>, ProofError> {
        verify_air::<EF, A, AP>(
            verifier_state,
            self,
            univariate_skips,
            log_n_rows,
            column_groups,
        )
    }
}

fn verify_many_unstructured_columns<EF: ExtensionField<PF<EF>>>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    univariate_skips: usize,
    inner_sums: Vec<EF>,
    column_groups: &[Range<usize>],
    outer_sumcheck_point: &MultilinearPoint<EF>,
    outer_selector_evals: &[EF],
    log_length: usize,
) -> Result<Vec<Evaluation<EF>>, ProofError> {
    let max_columns_per_group = column_groups.iter().map(|g| g.len()).max().unwrap();

    let log_max_columns_per_group = log2_ceil_usize(max_columns_per_group);
    let columns_batching_scalars = verifier_state.sample_vec(log_max_columns_per_group);

    let mut all_sub_evals = vec![];
    for group in column_groups {
        let sub_evals = verifier_state.next_extension_scalars_vec(1 << univariate_skips)?;

        if dot_product::<EF, _, _>(
            sub_evals.iter().copied(),
            outer_selector_evals.iter().copied(),
        ) != dot_product::<EF, _, _>(
            inner_sums[group.clone()].iter().copied(),
            eval_eq(from_end(
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

    let epsilons = MultilinearPoint(verifier_state.sample_vec(univariate_skips));

    let mut evaluations_remaining_to_verify = vec![];
    for (j, group) in column_groups.iter().enumerate() {
        let final_value = all_sub_evals[j].evaluate(&epsilons);
        let final_point = MultilinearPoint(
            [
                from_end(&columns_batching_scalars, log2_ceil_usize(group.len())).to_vec(),
                epsilons.0.clone(),
                outer_sumcheck_point[1..log_length - univariate_skips + 1].to_vec(),
            ]
            .concat(),
        );
        evaluations_remaining_to_verify.push(Evaluation::new(final_point, final_value));
    }

    Ok(evaluations_remaining_to_verify)
}

#[derive(Debug)]
struct StructuredColumnsArgs<'a, EF> {
    n_columns: usize,
    univariate_skips: usize,
    all_inner_sums: &'a [EF],
    column_groups: &'a [Range<usize>],
    outer_sumcheck_challenge: &'a Evaluation<EF>,
    outer_selector_evals: &'a [EF],
    log_n_rows: usize,
}

fn verify_structured_columns<EF: ExtensionField<PF<EF>>>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    args: StructuredColumnsArgs<'_, EF>,
) -> Result<Vec<Evaluation<EF>>, ProofError> {
    let StructuredColumnsArgs {
        n_columns,
        univariate_skips,
        all_inner_sums,
        column_groups,
        outer_sumcheck_challenge,
        outer_selector_evals,
        log_n_rows,
    } = args;
    let log_n_groups = log2_ceil_usize(column_groups.len());
    let max_columns_per_group = Iterator::max(column_groups.iter().map(|g| g.len())).unwrap();
    let log_max_columns_per_group = log2_ceil_usize(max_columns_per_group);
    let batching_scalars = verifier_state.sample_vec(log_n_groups + log_max_columns_per_group);
    let alpha = verifier_state.sample();

    let poly_eq_batching_scalars = eval_eq(&batching_scalars);
    let mut column_scalars = vec![];
    let mut index = 0;
    for group in column_groups {
        column_scalars.extend(
            poly_eq_batching_scalars
                .iter()
                .skip(index)
                .take(group.len())
                .copied(),
        );
        index += max_columns_per_group.next_power_of_two();
    }

    let all_witness_up = &all_inner_sums[..n_columns];
    let all_witness_down = &all_inner_sums[n_columns..];

    let sub_evals = verifier_state.next_extension_scalars_vec(1 << univariate_skips)?;

    if dot_product::<EF, _, _>(
        sub_evals.iter().copied(),
        outer_selector_evals.iter().copied(),
    ) != dot_product::<EF, _, _>(
        all_witness_up.iter().copied(),
        column_scalars.iter().copied(),
    ) + dot_product::<EF, _, _>(
        all_witness_down.iter().copied(),
        column_scalars.iter().copied(),
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

    let mut evaluations_remaining_to_verify = vec![];
    for group in column_groups {
        let point = MultilinearPoint(
            [
                from_end(
                    &batching_scalars[log_n_groups..],
                    log2_ceil_usize(group.len()),
                )
                .to_vec(),
                inner_sumcheck_stement.point.0.clone(),
            ]
            .concat(),
        );
        let value = verifier_state.next_extension_scalar()?;
        evaluations_remaining_to_verify.push(Evaluation { point, value });
    }

    assert_eq!(
        final_value,
        dot_product(
            eval_eq(&batching_scalars[..log_n_groups]).into_iter(),
            column_groups
                .iter()
                .enumerate()
                .map(|(i, group)| evaluations_remaining_to_verify[i].value
                    * batching_scalars[log_n_groups
                        ..log_n_groups + log_max_columns_per_group - log2_ceil_usize(group.len())]
                        .iter()
                        .map(|&x| EF::ONE - x)
                        .product::<EF>())
        )
    );
    Ok(evaluations_remaining_to_verify)
}
