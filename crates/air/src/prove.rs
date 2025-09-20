use std::any::TypeId;

use p3_air::BaseAir;
use p3_field::{ExtensionField, Field, cyclic_subgroup_known_order, dot_product};
use p3_util::log2_ceil_usize;
use sumcheck::{MleGroup, MleGroupOwned, MleGroupRef, ProductComputation};
use tracing::{info_span, instrument};
use utils::PF;
use utils::{FSProver, add_multilinears, from_end, multilinears_linear_combination};
use whir_p3::fiat_shamir::FSChallenger;
use whir_p3::poly::evals::{eval_eq, fold_multilinear, scale_poly};
use whir_p3::poly::multilinear::Evaluation;
use whir_p3::poly::{evals::EvaluationsList, multilinear::MultilinearPoint};

use crate::witness::AirWitness;
use crate::{NormalAir, PackedAir};
use crate::{
    uni_skip_utils::{matrix_down_folded, matrix_up_folded},
    utils::{column_down, column_up, columns_up_and_down},
};

use super::table::AirTable;

/*

cf https://eprint.iacr.org/2023/552.pdf and https://solvable.group/posts/super-air/#fnref:1

*/

#[instrument(name = "prove air", skip_all)]
fn prove_air<
    'a,
    WF: ExtensionField<PF<EF>>, // witness field
    EF: ExtensionField<PF<EF>> + ExtensionField<WF>,
    A: NormalAir<EF>,
    AP: PackedAir<EF>,
>(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    univariate_skips: usize,
    table: &AirTable<EF, A, AP>,
    witness: AirWitness<'a, WF>,
) -> Vec<Evaluation<EF>> {
    assert!(
        univariate_skips < witness.log_n_rows(),
        "TODO handle the case UNIVARIATE_SKIPS >= log_length"
    );

    let structured_air = <A as BaseAir<PF<EF>>>::structured(&table.air);

    let log_length = witness.log_n_rows();

    let constraints_batching_scalar = prover_state.sample();

    let constraints_batching_scalars =
        cyclic_subgroup_known_order(constraints_batching_scalar, table.n_constraints)
            .collect::<Vec<_>>();

    let n_sc_rounds = log_length + 1 - univariate_skips;

    let zerocheck_challenges = prover_state.sample_vec(n_sc_rounds);

    let columns_for_zero_check: MleGroup<'_, EF> = if TypeId::of::<WF>() == TypeId::of::<PF<EF>>() {
        let columns =
            unsafe { std::mem::transmute::<&Vec<&'a [WF]>, &Vec<&'a [PF<EF>]>>(&witness.cols) };
        if structured_air {
            MleGroupOwned::Base(columns_up_and_down(columns)).into()
        } else {
            MleGroupRef::Base(columns.clone()).into()
        }
    } else {
        assert!(TypeId::of::<WF>() == TypeId::of::<EF>());
        let columns =
            unsafe { std::mem::transmute::<&Vec<&'a [WF]>, &Vec<&'a [EF]>>(&witness.cols) };
        if structured_air {
            MleGroupOwned::Extension(columns_up_and_down(columns)).into()
        } else {
            MleGroupRef::Extension(columns.clone()).into()
        }
    };

    let columns_for_zero_check_packed = columns_for_zero_check.by_ref().pack();

    let (outer_sumcheck_challenge, inner_sums, _) = info_span!("zerocheck").in_scope(|| {
        sumcheck::prove::<_, _, _, _>(
            univariate_skips,
            columns_for_zero_check_packed,
            &table.air,
            &table.air_packed,
            &constraints_batching_scalars,
            Some((zerocheck_challenges, None)),
            true,
            prover_state,
            EF::ZERO,
            None,
        )
    });

    prover_state.add_extension_scalars(&inner_sums);

    if structured_air {
        open_structured_columns(
            prover_state,
            univariate_skips,
            &witness,
            &outer_sumcheck_challenge,
        )
    } else {
        open_unstructured_columns(
            prover_state,
            univariate_skips,
            &witness,
            &outer_sumcheck_challenge,
        )
    }
}

impl<EF: ExtensionField<PF<EF>>, A: NormalAir<EF>, AP: PackedAir<EF>> AirTable<EF, A, AP> {
    #[instrument(name = "air: prove in base", skip_all)]
    pub fn prove_base<'a>(
        &self,
        prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
        univariate_skips: usize,
        witness: AirWitness<'a, PF<EF>>,
    ) -> Vec<Evaluation<EF>> {
        prove_air::<PF<EF>, EF, A, AP>(prover_state, univariate_skips, self, witness)
    }

    #[instrument(name = "air: prove in extension", skip_all)]
    pub fn prove_extension<'a>(
        &self,
        prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
        univariate_skips: usize,
        witness: AirWitness<'a, EF>,
    ) -> Vec<Evaluation<EF>> {
        prove_air::<EF, EF, A, AP>(prover_state, univariate_skips, self, witness)
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
            &eval_eq(from_end(
                columns_batching_scalars,
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
fn open_unstructured_columns<
    'a,
    WF: ExtensionField<PF<EF>>,
    EF: ExtensionField<PF<EF>> + ExtensionField<WF>,
>(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    univariate_skips: usize,
    witness: &AirWitness<'a, WF>,
    outer_sumcheck_challenge: &[EF],
) -> Vec<Evaluation<EF>> {
    let columns_batching_scalars =
        prover_state.sample_vec(log2_ceil_usize(witness.max_columns_per_group()));

    let sub_evals = eval_unstructured_column_groups(
        prover_state,
        univariate_skips,
        witness,
        outer_sumcheck_challenge,
        &columns_batching_scalars,
    );

    let epsilons = MultilinearPoint(prover_state.sample_vec(univariate_skips));

    let mut evaluations_remaining_to_prove = vec![];
    for (group, sub_evals) in witness.column_groups.iter().zip(sub_evals) {
        assert_eq!(sub_evals.len(), 1 << epsilons.len());

        evaluations_remaining_to_prove.push(Evaluation::new(
            [
                from_end(&columns_batching_scalars, log2_ceil_usize(group.len())).to_vec(),
                epsilons.0.clone(),
                outer_sumcheck_challenge[1..witness.log_n_rows() - univariate_skips + 1].to_vec(),
            ]
            .concat(),
            sub_evals.evaluate(&epsilons),
        ));
    }
    evaluations_remaining_to_prove
}

#[instrument(skip_all)]
fn open_structured_columns<'a, EF: ExtensionField<PF<EF>> + ExtensionField<IF>, IF: Field>(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    univariate_skips: usize,
    witness: &AirWitness<'a, IF>,
    outer_sumcheck_challenge: &[EF],
) -> Vec<Evaluation<EF>> {
    let log_n_groups = log2_ceil_usize(witness.column_groups.len());
    let batching_scalars =
        prover_state.sample_vec(log_n_groups + witness.log_max_columns_per_group());
    let alpha = prover_state.sample();

    let poly_eq_batching_scalars = eval_eq(&batching_scalars);
    let mut column_scalars = vec![];
    let mut index = 0;
    for group in &witness.column_groups {
        column_scalars.extend(
            poly_eq_batching_scalars
                .iter()
                .skip(index)
                .take(group.len())
                .copied(),
        );
        index += witness.max_columns_per_group().next_power_of_two();
    }

    let batched_column = multilinears_linear_combination(&witness.cols, &column_scalars);
    let batched_column_mixed = add_multilinears(
        &column_up(&batched_column),
        &scale_poly(&column_down(&batched_column), alpha),
    );
    // TODO do not recompute this (we can deduce it from already computed values)
    let sub_evals = fold_multilinear(
        &batched_column_mixed,
        &MultilinearPoint(
            outer_sumcheck_challenge[1..witness.log_n_rows() - univariate_skips + 1].to_vec(),
        ),
    );
    prover_state.add_extension_scalars(&sub_evals);

    let epsilons = prover_state.sample_vec(univariate_skips);

    let point = [
        epsilons,
        outer_sumcheck_challenge[1..witness.log_n_rows() - univariate_skips + 1].to_vec(),
    ]
    .concat();

    // TODO do not recompute this (we can deduce it from already computed values)
    let inner_sum = batched_column_mixed.evaluate(&MultilinearPoint(point.clone()));

    let inner_mle = MleGroupOwned::Extension(vec![
        add_multilinears(
            &matrix_up_folded(&point),
            &scale_poly(&matrix_down_folded(&point), alpha),
        ),
        batched_column,
    ]);

    let n_groups = witness.column_groups.len();
    let (inner_challenges, inner_evals, _) = sumcheck::prove::<EF, _, _, _>(
        1,
        inner_mle,
        &ProductComputation,
        &ProductComputation,
        &[],
        None,
        false,
        prover_state,
        inner_sum,
        None,
    );

    // TODO using inner_evals[1], we can avoid 1 of the evaluations below (the last one)

    let mut evaluations_remaining_to_prove = vec![];
    for i in 0..n_groups {
        let group = &witness.column_groups[i];
        let point = MultilinearPoint(
            [
                from_end(
                    &batching_scalars[log_n_groups..],
                    log2_ceil_usize(group.len()),
                )
                .to_vec(),
                inner_challenges.0.clone(),
            ]
            .concat(),
        );
        let value = {
            let mut padded_group = IF::zero_vec(group.len().next_power_of_two() * witness.n_rows());
            for (i, col) in witness.cols[group.clone()].iter().enumerate() {
                padded_group[i * witness.n_rows()..(i + 1) * witness.n_rows()].copy_from_slice(col);
            }
            padded_group.evaluate(&point)
        };
        prover_state.add_extension_scalars(&[value]);
        evaluations_remaining_to_prove.push(Evaluation { point, value });
    }

    assert_eq!(
        inner_evals[1],
        dot_product(
            eval_eq(&batching_scalars[..log_n_groups]).into_iter(),
            (0..n_groups).map(|i| evaluations_remaining_to_prove[i].value
                * batching_scalars[log_n_groups
                    ..log_n_groups + witness.log_max_columns_per_group()
                        - log2_ceil_usize(witness.column_groups[i].len())]
                    .iter()
                    .map(|&x| EF::ONE - x)
                    .product::<EF>())
        )
    );

    evaluations_remaining_to_prove
}
