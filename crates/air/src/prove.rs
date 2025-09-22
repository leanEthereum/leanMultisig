use std::any::TypeId;

use p3_air::BaseAir;
use p3_field::{ExtensionField, Field, cyclic_subgroup_known_order};
use p3_util::{log2_ceil_usize, log2_strict_usize};
use sumcheck::{MleGroup, MleGroupOwned, MleGroupRef, ProductComputation};
use tracing::{info_span, instrument};
use utils::PF;
use utils::{FSProver, add_multilinears, multilinears_linear_combination};
use whir_p3::fiat_shamir::FSChallenger;
use whir_p3::poly::evals::{eval_eq, fold_multilinear, scale_poly};
use whir_p3::poly::{evals::EvaluationsList, multilinear::MultilinearPoint};

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
    witness: &[&'a [WF]],
) -> (MultilinearPoint<EF>, Vec<EF>) {
    let n_rows = witness[0].len();
    assert!(witness.iter().all(|col| col.len() == n_rows));
    let log_n_rows = log2_strict_usize(n_rows);
    assert!(
        univariate_skips < log_n_rows,
        "TODO handle the case UNIVARIATE_SKIPS >= log_length"
    );

    let structured_air = <A as BaseAir<PF<EF>>>::structured(&table.air);

    let constraints_batching_scalar = prover_state.sample();

    let constraints_batching_scalars =
        cyclic_subgroup_known_order(constraints_batching_scalar, table.n_constraints)
            .collect::<Vec<_>>();

    let n_sc_rounds = log_n_rows + 1 - univariate_skips;

    let zerocheck_challenges = prover_state.sample_vec(n_sc_rounds);

    let columns_for_zero_check: MleGroup<'_, EF> = if TypeId::of::<WF>() == TypeId::of::<PF<EF>>() {
        let columns = unsafe { std::mem::transmute::<&[&[WF]], &[&[PF<EF>]]>(witness) };
        if structured_air {
            MleGroupOwned::Base(columns_up_and_down(columns)).into()
        } else {
            MleGroupRef::Base(columns.to_vec()).into()
        }
    } else {
        assert!(TypeId::of::<WF>() == TypeId::of::<EF>());
        let columns = unsafe { std::mem::transmute::<&[&'a [WF]], &[&'a [EF]]>(witness) };
        if structured_air {
            MleGroupOwned::Extension(columns_up_and_down(columns)).into()
        } else {
            MleGroupRef::Extension(columns.to_vec()).into()
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
            witness,
            &outer_sumcheck_challenge,
        )
    } else {
        open_unstructured_columns(
            prover_state,
            univariate_skips,
            witness,
            &outer_sumcheck_challenge,
        )
    }
}

impl<EF: ExtensionField<PF<EF>>, A: NormalAir<EF>, AP: PackedAir<EF>> AirTable<EF, A, AP> {
    #[instrument(name = "air: prove in base", skip_all)]
    pub fn prove_base(
        &self,
        prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
        univariate_skips: usize,
        witness: &[&[PF<EF>]],
    ) -> (MultilinearPoint<EF>, Vec<EF>) {
        prove_air::<PF<EF>, EF, A, AP>(prover_state, univariate_skips, self, witness)
    }

    #[instrument(name = "air: prove in extension", skip_all)]
    pub fn prove_extension(
        &self,
        prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
        univariate_skips: usize,
        witness: &[&[EF]],
    ) -> (MultilinearPoint<EF>, Vec<EF>) {
        prove_air::<EF, EF, A, AP>(prover_state, univariate_skips, self, witness)
    }
}

#[instrument(skip_all)]
fn open_unstructured_columns<
    WF: ExtensionField<PF<EF>>,
    EF: ExtensionField<PF<EF>> + ExtensionField<WF>,
>(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    univariate_skips: usize,
    witness: &[&[WF]],
    outer_sumcheck_challenge: &[EF],
) -> (MultilinearPoint<EF>, Vec<EF>) {
    let log_n_rows = log2_strict_usize(witness[0].len());

    let columns_batching_scalars = prover_state.sample_vec(log2_ceil_usize(witness.len()));

    let batched_column = multilinears_linear_combination(
        witness,
        &eval_eq(&columns_batching_scalars)[..witness.len()],
    );

    // TODO opti
    let sub_evals = fold_multilinear(
        &batched_column,
        &MultilinearPoint(outer_sumcheck_challenge[1..log_n_rows - univariate_skips + 1].to_vec()),
    );

    prover_state.add_extension_scalars(&sub_evals);

    let epsilons = MultilinearPoint(prover_state.sample_vec(univariate_skips));
    let common_point = MultilinearPoint(
        [
            epsilons.0.clone(),
            outer_sumcheck_challenge[1..log_n_rows - univariate_skips + 1].to_vec(),
        ]
        .concat(),
    );

    let evaluations_remaining_to_prove = witness
        .iter()
        .map(|col| col.evaluate(&common_point))
        .collect::<Vec<_>>();
    prover_state.add_extension_scalars(&evaluations_remaining_to_prove);

    (common_point, evaluations_remaining_to_prove)
}

#[instrument(skip_all)]
fn open_structured_columns<EF: ExtensionField<PF<EF>> + ExtensionField<IF>, IF: Field>(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    univariate_skips: usize,
    witness: &[&[IF]],
    outer_sumcheck_challenge: &[EF],
) -> (MultilinearPoint<EF>, Vec<EF>) {
    let n_columns = witness.len();
    let n_rows = witness[0].len();
    let log_n_rows = log2_strict_usize(n_rows);
    let batching_scalars = prover_state.sample_vec(log2_ceil_usize(n_columns));
    let alpha = prover_state.sample();

    let poly_eq_batching_scalars = eval_eq(&batching_scalars);

    let batched_column =
        multilinears_linear_combination(witness, &poly_eq_batching_scalars[..n_columns]);
    let batched_column_mixed = add_multilinears(
        &column_up(&batched_column),
        &scale_poly(&column_down(&batched_column), alpha),
    );
    // TODO do not recompute this (we can deduce it from already computed values)
    let sub_evals = fold_multilinear(
        &batched_column_mixed,
        &MultilinearPoint(outer_sumcheck_challenge[1..log_n_rows - univariate_skips + 1].to_vec()),
    );
    prover_state.add_extension_scalars(&sub_evals);

    let epsilons = prover_state.sample_vec(univariate_skips);

    let point = [
        epsilons,
        outer_sumcheck_challenge[1..log_n_rows - univariate_skips + 1].to_vec(),
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

    let (inner_challenges, _, _) = sumcheck::prove::<EF, _, _, _>(
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

    let evaluations_remaining_to_prove = witness
        .iter()
        .map(|col| col.evaluate(&inner_challenges))
        .collect::<Vec<_>>();
    prover_state.add_extension_scalars(&evaluations_remaining_to_prove);

    (inner_challenges, evaluations_remaining_to_prove)
}
