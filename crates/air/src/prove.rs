use p3_field::{ExtensionField, Field, cyclic_subgroup_known_order};
use p3_util::log2_ceil_usize;
use sumcheck::{MleGroup, MleGroupOwned, MleGroupRef, ProductComputation};
use tracing::{info_span, instrument};
use utils::{
    Evaluation, FSProver, PF, add_multilinears, from_end, multilinears_linear_combination,
};
use whir_p3::{
    fiat_shamir::FSChallenger,
    poly::{
        evals::{EvaluationsList, eval_eq, fold_multilinear, scale_poly},
        multilinear::MultilinearPoint,
    },
};

use super::table::AirTable;
use crate::{
    MyAir,
    uni_skip_utils::{matrix_down_folded, matrix_up_folded},
    utils::{column_down, column_up, columns_up_and_down},
    witness::AirWitness,
};

/*

cf https://eprint.iacr.org/2023/552.pdf and https://solvable.group/posts/super-air/#fnref:1

*/

#[instrument(name = "air: prove many", skip_all)]
pub fn prove_many_air_2<'a, EF: ExtensionField<PF<EF>>, A1: MyAir<EF>, A2: MyAir<EF>>(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    univariate_skips: usize,
    tables_1: &[&AirTable<EF, A1>],
    tables_2: &[&AirTable<EF, A2>],
    witnesses_1: &[AirWitness<'a, PF<EF>>],
    witnesses_2: &[AirWitness<'a, PF<EF>>],
) -> Vec<Vec<Evaluation<EF>>> {
    prove_many_air_3::<_, _, _, A2>(
        prover_state,
        univariate_skips,
        tables_1,
        tables_2,
        &[],
        witnesses_1,
        witnesses_2,
        &[],
    )
}

#[instrument(name = "air: prove many", skip_all)]
pub fn prove_many_air_3<
    'a,
    EF: ExtensionField<PF<EF>>,
    A1: MyAir<EF>,
    A2: MyAir<EF>,
    A3: MyAir<EF>,
>(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    univariate_skips: usize,
    tables_1: &[&AirTable<EF, A1>],
    tables_2: &[&AirTable<EF, A2>],
    tables_3: &[&AirTable<EF, A3>],
    witnesses_1: &[AirWitness<'a, PF<EF>>],
    witnesses_2: &[AirWitness<'a, PF<EF>>],
    witnesses_3: &[AirWitness<'a, EF>],
) -> Vec<Vec<Evaluation<EF>>> {
    let n_tables = tables_1.len() + tables_2.len() + tables_3.len();
    assert_eq!(
        n_tables,
        witnesses_1.len() + witnesses_2.len() + witnesses_3.len()
    );
    for i in 0..tables_1.len() {
        assert!(
            univariate_skips < witnesses_1[i].log_n_rows(),
            "TODO handle the case UNIVARIATE_SKIPS >= log_length"
        );
    }
    for i in 0..tables_2.len() {
        assert!(
            univariate_skips < witnesses_2[i].log_n_rows(),
            "TODO handle the case UNIVARIATE_SKIPS >= log_length"
        );
    }
    for i in 0..tables_3.len() {
        assert!(
            univariate_skips < witnesses_3[i].log_n_rows(),
            "TODO handle the case UNIVARIATE_SKIPS >= log_length"
        );
    }
    let structured_air = if tables_1.len() > 0 {
        tables_1[0].air.structured()
    } else if tables_2.len() > 0 {
        tables_2[0].air.structured()
    } else {
        tables_3[0].air.structured()
    };
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

    let log_lengths_1 = witnesses_1
        .iter()
        .map(|w| w.log_n_rows())
        .collect::<Vec<_>>();
    let log_lengths_2 = witnesses_2
        .iter()
        .map(|w| w.log_n_rows())
        .collect::<Vec<_>>();
    let log_lengths_3 = witnesses_3
        .iter()
        .map(|w| w.log_n_rows())
        .collect::<Vec<_>>();

    let max_n_constraints = Iterator::max(
        tables_1
            .iter()
            .map(|t| t.n_constraints)
            .chain(tables_2.iter().map(|t| t.n_constraints))
            .chain(tables_3.iter().map(|t| t.n_constraints)),
    )
    .unwrap();

    let constraints_batching_scalar = prover_state.sample();

    let constraints_batching_scalars =
        cyclic_subgroup_known_order(constraints_batching_scalar, max_n_constraints)
            .collect::<Vec<_>>();

    let n_sc_rounds = log_lengths_1
        .iter()
        .chain(&log_lengths_2)
        .chain(&log_lengths_3)
        .map(|l| l + 1 - univariate_skips)
        .collect::<Vec<_>>();

    let n_zerocheck_challenges = *Iterator::max(n_sc_rounds.iter()).unwrap();

    let global_zerocheck_challenges = prover_state.sample_vec(n_zerocheck_challenges);

    let mut columns_for_zero_check = witnesses_1
        .iter()
        .chain(witnesses_2)
        .map(|w| {
            if structured_air {
                MleGroupOwned::Base(columns_up_and_down(w)).into()
            } else {
                MleGroupRef::Base(w.cols.clone()).into()
            }
        })
        .collect::<Vec<MleGroup<'_, EF>>>();
    columns_for_zero_check.extend(witnesses_3.iter().map(|w| {
        if structured_air {
            MleGroupOwned::Extension(columns_up_and_down(w)).into()
        } else {
            MleGroupRef::Extension(w.cols.clone()).into()
        }
    }));

    let columns_for_zero_check_packed = columns_for_zero_check
        .iter()
        .map(|c| c.by_ref().pack())
        .collect::<Vec<_>>();

    let all_zerocheck_challenges = (0..n_tables)
        .map(|i| {
            Some((
                global_zerocheck_challenges[0..n_sc_rounds[i]].to_vec(),
                None,
            ))
        })
        .collect::<Vec<_>>();
    let (outer_sumcheck_challenge, all_inner_sums, _) = info_span!("zerocheck").in_scope(|| {
        sumcheck::prove_in_parallel_3::<EF, _, _, _, _>(
            vec![univariate_skips; n_tables],
            columns_for_zero_check_packed,
            tables_1.iter().map(|t| &t.air).collect::<Vec<_>>(),
            tables_2.iter().map(|t| &t.air).collect::<Vec<_>>(),
            tables_3.iter().map(|t| &t.air).collect::<Vec<_>>(),
            vec![&constraints_batching_scalars; n_tables],
            all_zerocheck_challenges,
            vec![true; n_tables],
            prover_state,
            vec![EF::ZERO; n_tables],
            vec![None; n_tables],
            true,
        )
    });

    for inner_sums in &all_inner_sums {
        prover_state.add_extension_scalars(inner_sums);
    }

    if structured_air {
        // TODO inner sumchecks in parallel between tables(not usefull in the current protocol but cleaner, more coherent)
        let mut evaluations_remaining_to_prove = vec![];
        for witness in witnesses_1.iter().chain(witnesses_2) {
            evaluations_remaining_to_prove.push(open_structured_columns(
                prover_state,
                univariate_skips,
                witness,
                &outer_sumcheck_challenge,
            ));
        }
        for witness in witnesses_3 {
            evaluations_remaining_to_prove.push(open_structured_columns::<EF, EF>(
                prover_state,
                univariate_skips,
                witness,
                &outer_sumcheck_challenge,
            ));
        }
        evaluations_remaining_to_prove
    } else {
        open_unstructured_columns(
            prover_state,
            univariate_skips,
            witnesses_1,
            witnesses_2,
            witnesses_3,
            &outer_sumcheck_challenge,
        )
    }
}

impl<EF: ExtensionField<PF<EF>>, A: MyAir<EF>> AirTable<EF, A> {
    #[instrument(name = "air: prove base", skip_all)]
    pub fn prove_base<'a>(
        &self,
        prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
        univariate_skips: usize,
        witness: AirWitness<'a, PF<EF>>,
    ) -> Vec<Evaluation<EF>> {
        let mut res = prove_many_air_3::<EF, A, A, A>(
            prover_state,
            univariate_skips,
            &[self],
            &[],
            &[],
            &[witness],
            &[],
            &[],
        );
        assert_eq!(res.len(), 1);
        res.pop().unwrap()
    }

    #[instrument(name = "air: prove base", skip_all)]
    pub fn prove_extension<'a>(
        &self,
        prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
        univariate_skips: usize,
        witness: AirWitness<'a, EF>,
    ) -> Vec<Evaluation<EF>> {
        let mut res = prove_many_air_3::<EF, A, A, A>(
            prover_state,
            univariate_skips,
            &[],
            &[],
            &[self],
            &[],
            &[],
            &[witness],
        );
        assert_eq!(res.len(), 1);
        res.pop().unwrap()
    }
}

fn eval_unstructured_column_groups<EF: ExtensionField<PF<EF>> + ExtensionField<IF>, IF: Field>(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    univariate_skips: usize,
    witnesses: &AirWitness<'_, IF>,
    outer_sumcheck_challenge: &[EF],
    columns_batching_scalars: &[EF],
) -> Vec<Vec<EF>> {
    let mut all_sub_evals = vec![];
    for group in &witnesses.column_groups {
        let batched_column = multilinears_linear_combination(
            &witnesses.cols[group.clone()],
            &eval_eq(&from_end(
                &columns_batching_scalars,
                log2_ceil_usize(group.len()),
            ))[..group.len()],
        );

        // TODO opti
        let sub_evals = fold_multilinear(
            &batched_column,
            &MultilinearPoint(
                outer_sumcheck_challenge[1..witnesses.log_n_rows() - univariate_skips + 1].to_vec(),
            ),
        );

        prover_state.add_extension_scalars(&sub_evals);
        all_sub_evals.push(sub_evals);
    }
    all_sub_evals
}

#[instrument(skip_all)]
fn open_unstructured_columns<'a, EF: ExtensionField<PF<EF>>>(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    univariate_skips: usize,
    witnesses_1: &[AirWitness<'a, PF<EF>>],
    witnesses_2: &[AirWitness<'a, PF<EF>>],
    witnesses_3: &[AirWitness<'a, EF>],
    outer_sumcheck_challenge: &[EF],
) -> Vec<Vec<Evaluation<EF>>> {
    let max_columns_per_group = Iterator::max(
        witnesses_1
            .iter()
            .chain(witnesses_2)
            .map(|w| w.max_columns_per_group())
            .chain(witnesses_3.iter().map(|w| w.max_columns_per_group())),
    )
    .unwrap();
    let columns_batching_scalars = prover_state.sample_vec(log2_ceil_usize(max_columns_per_group));

    let mut all_sub_evals = vec![];
    for witness in witnesses_1.iter().chain(witnesses_2) {
        all_sub_evals.push(eval_unstructured_column_groups(
            prover_state,
            univariate_skips,
            witness,
            outer_sumcheck_challenge,
            &columns_batching_scalars,
        ));
    }
    for witness in witnesses_3 {
        all_sub_evals.push(eval_unstructured_column_groups::<EF, EF>(
            prover_state,
            univariate_skips,
            witness,
            outer_sumcheck_challenge,
            &columns_batching_scalars,
        ));
    }

    let epsilons = MultilinearPoint(prover_state.sample_vec(univariate_skips));

    let column_groups_and_log_n_rows = witnesses_1
        .iter()
        .chain(witnesses_2)
        .map(|w| (&w.column_groups, w.log_n_rows()))
        .chain(
            witnesses_3
                .iter()
                .map(|w| (&w.column_groups, w.log_n_rows())),
        );
    let mut all_evaluations_remaining_to_prove = vec![];

    for ((column_groups, log_n_rows), all_sub_evals) in
        column_groups_and_log_n_rows.zip(all_sub_evals)
    {
        let mut evaluations_remaining_to_prove = vec![];
        for (group, sub_evals) in column_groups.iter().zip(all_sub_evals) {
            assert_eq!(sub_evals.len(), 1 << epsilons.len());

            evaluations_remaining_to_prove.push(Evaluation {
                point: MultilinearPoint(
                    [
                        from_end(&columns_batching_scalars, log2_ceil_usize(group.len())).to_vec(),
                        epsilons.0.clone(),
                        outer_sumcheck_challenge[1..log_n_rows - univariate_skips + 1].to_vec(),
                    ]
                    .concat(),
                ),
                value: sub_evals.evaluate(&epsilons),
            });
        }
        all_evaluations_remaining_to_prove.push(evaluations_remaining_to_prove);
    }
    all_evaluations_remaining_to_prove
}

#[instrument(skip_all)]
fn open_structured_columns<'a, EF: ExtensionField<PF<EF>> + ExtensionField<IF>, IF: Field>(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    univariate_skips: usize,
    witness: &AirWitness<'a, IF>,
    outer_sumcheck_challenge: &[EF],
) -> Vec<Evaluation<EF>> {
    let columns_batching_scalars = prover_state.sample_vec(witness.log_max_columns_per_group());
    let alpha = prover_state.sample();

    let mut all_inner_mles = vec![];
    let mut all_inner_sums = vec![];
    let mut all_batched_columns = vec![];
    let mut all_batched_columns_mixed = vec![];
    for group in &witness.column_groups {
        let batched_column = multilinears_linear_combination(
            &witness.cols[group.clone()],
            &eval_eq(&from_end(
                &columns_batching_scalars,
                log2_ceil_usize(group.len()),
            ))[..group.len()],
        );
        all_batched_columns.push(batched_column.clone());
        let batched_column_mixed = add_multilinears(
            &column_up(&batched_column),
            &scale_poly(&column_down(&batched_column), alpha),
        );
        all_batched_columns_mixed.push(batched_column_mixed.clone());

        // TODO opti
        let sub_evals = fold_multilinear(
            &batched_column_mixed,
            &MultilinearPoint(
                outer_sumcheck_challenge[1..witness.log_n_rows() - univariate_skips + 1].to_vec(),
            ),
        );

        prover_state.add_extension_scalars(&sub_evals);
    }

    let epsilons = prover_state.sample_vec(univariate_skips);

    for (batched_column, batched_column_mixed) in all_batched_columns
        .into_iter()
        .zip(all_batched_columns_mixed)
    {
        let point = [
            epsilons.clone(),
            outer_sumcheck_challenge[1..witness.log_n_rows() - univariate_skips + 1].to_vec(),
        ]
        .concat();
        let mles_for_inner_sumcheck = vec![
            add_multilinears(
                &matrix_up_folded(&point),
                &scale_poly(&matrix_down_folded(&point), alpha),
            ),
            batched_column,
        ];

        // TODO do not recompute
        let inner_sum = info_span!("inner sum evaluation")
            .in_scope(|| batched_column_mixed.evaluate(&MultilinearPoint(point.clone())));

        all_inner_mles.push(MleGroupOwned::Extension(mles_for_inner_sumcheck));
        all_inner_sums.push(inner_sum);
    }
    let n_groups = witness.column_groups.len();
    let (inner_challenges, all_inner_evals, _) = sumcheck::prove_in_parallel_1::<EF, _, _>(
        vec![1; n_groups],
        all_inner_mles,
        vec![&ProductComputation; n_groups],
        vec![&[]; n_groups],
        vec![None; n_groups],
        vec![false; n_groups],
        prover_state,
        all_inner_sums,
        vec![None; n_groups],
        true,
    );

    let mut evaluations_remaining_to_prove = vec![];
    for i in 0..n_groups {
        let group = &witness.column_groups[i];
        let point = MultilinearPoint(
            [
                from_end(&columns_batching_scalars, log2_ceil_usize(group.len())).to_vec(),
                inner_challenges.0.clone(),
            ]
            .concat(),
        );
        let value = all_inner_evals[i][1];
        evaluations_remaining_to_prove.push(Evaluation { point, value });
    }
    evaluations_remaining_to_prove
}
