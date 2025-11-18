use multilinear_toolkit::prelude::*;
use p3_air::Air;
use p3_util::{log2_ceil_usize, log2_strict_usize};
use tracing::{info_span, instrument};
use utils::{FSProver, fold_multilinear_chunks, multilinears_linear_combination};

use crate::{uni_skip_utils::matrix_next_mle_folded, utils::column_shifted};

use super::table::AirTable;

/*

cf https://eprint.iacr.org/2023/552.pdf and https://solvable.group/posts/super-air/#fnref:1

*/

#[instrument(name = "prove air", skip_all)]
#[allow(clippy::too_many_arguments)]
pub fn prove_air<EF: ExtensionField<PF<EF>>, A: Air>(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    table: &AirTable<EF, A>,
    univariate_skips: usize,
    columns_f: &[&[PF<EF>]],
    columns_ef: &[&[EF]],
    last_row_shifted: &[EF],
    virtual_column_statements: Option<MultiEvaluation<EF>>, // point should be randomness generated after committing to the columns
    store_intermediate_foldings: bool,
) -> (MultilinearPoint<EF>, Vec<EF>) {
    let n_rows = columns_f[0].len();
    assert!(columns_f.iter().all(|col| col.len() == n_rows));
    assert!(columns_ef.iter().all(|col| col.len() == n_rows));
    let log_n_rows = log2_strict_usize(n_rows);
    assert!(
        univariate_skips < log_n_rows,
        "TODO handle the case UNIVARIATE_SKIPS >= log_length"
    );

    let constraints_batching_scalar = prover_state.sample();

    let constraints_batching_scalars = constraints_batching_scalar
        .powers()
        .take(table.n_constraints() + virtual_column_statements.is_some() as usize)
        .collect();

    let n_sc_rounds = log_n_rows + 1 - univariate_skips;

    let zerocheck_challenges = virtual_column_statements
        .as_ref()
        .map(|st| st.point.0.clone())
        .unwrap_or_else(|| prover_state.sample_vec(n_sc_rounds));
    assert_eq!(zerocheck_challenges.len(), n_sc_rounds);

    let shifted_rows_f = table
        .down_column_indexes()
        .par_iter()
        .zip_eq(last_row_shifted)
        .filter(|(i, _)| **i < A::n_columns_f())
        .map(|(&col_index, &final_value)| {
            column_shifted(columns_f[col_index], final_value.as_base().unwrap())
        })
        .collect::<Vec<_>>();
    let shifted_rows_ef = table
        .down_column_indexes()
        .par_iter()
        .zip_eq(last_row_shifted)
        .filter(|(i, _)| **i >= A::n_columns_f())
        .map(|(&col_index, &final_value)| {
            column_shifted(columns_ef[col_index - A::n_columns_f()], final_value)
        })
        .collect::<Vec<_>>();

    let mut columns_up_down_f = columns_f.to_vec(); // orginal columns, followed by shifted ones
    columns_up_down_f.extend(shifted_rows_f.iter().map(Vec::as_slice));

    let mut columns_up_down_ef = columns_ef.to_vec(); // orginal columns, followed by shifted ones
    columns_up_down_ef.extend(shifted_rows_ef.iter().map(Vec::as_slice));

    let columns_up_down_group_f: MleGroupRef<'_, EF> =
        MleGroupRef::<'_, EF>::Base(columns_up_down_f);
    let columns_up_down_group_ef: MleGroupRef<'_, EF> =
        MleGroupRef::<'_, EF>::Extension(columns_up_down_ef);

    let columns_up_down_group_f_packed = columns_up_down_group_f.pack();
    let columns_up_down_group_ef_packed = columns_up_down_group_ef.pack();

    let (outer_sumcheck_challenge, inner_sums, _) = info_span!("zerocheck").in_scope(|| {
        sumcheck_prove(
            univariate_skips,
            columns_up_down_group_f_packed,
            Some(columns_up_down_group_ef_packed),
            &table.air,
            &constraints_batching_scalars,
            Some((zerocheck_challenges, None)),
            virtual_column_statements.is_none(),
            prover_state,
            virtual_column_statements
                .as_ref()
                .map(|st| dot_product(st.values.iter().copied(), constraints_batching_scalar.powers()))
                .unwrap_or_else(|| EF::ZERO),
            store_intermediate_foldings,
        )
    });

    prover_state.add_extension_scalars(&inner_sums);

    open_columns(
        prover_state,
        univariate_skips,
        &table.down_column_indexes(),
        columns_f,
        columns_ef,
        &outer_sumcheck_challenge,
    )
}

#[instrument(skip_all)]
fn open_columns<EF: ExtensionField<PF<EF>>>(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    univariate_skips: usize,
    columns_with_shift: &[usize],
    columns_f: &[&[PF<EF>]],
    columns_ef: &[&[EF]],
    outer_sumcheck_challenge: &[EF],
) -> (MultilinearPoint<EF>, Vec<EF>) {
    let n_up_down_columns = columns_f.len() + columns_ef.len() + columns_with_shift.len();
    let batching_scalars = prover_state.sample_vec(log2_ceil_usize(n_up_down_columns));

    let eval_eq_batching_scalars = eval_eq(&batching_scalars)[..n_up_down_columns].to_vec();

    let mut batched_column_up =
        multilinears_linear_combination(columns_f, &eval_eq_batching_scalars[..columns_f.len()]);
    if !columns_ef.is_empty() {
        let batched_column_up_ef = multilinears_linear_combination(
            columns_ef,
            &eval_eq_batching_scalars[columns_f.len()..][..columns_ef.len()],
        );
        batched_column_up
            .par_iter_mut()
            .zip(&batched_column_up_ef)
            .for_each(|(a, &b)| {
                *a += b;
            });
    }

    let columns_shifted_f = &columns_with_shift
        .iter()
        .filter(|&&i| i < columns_f.len())
        .map(|&i| columns_f[i])
        .collect::<Vec<_>>();
    let columns_shifted_ef = &columns_with_shift
        .iter()
        .filter(|&&i| i >= columns_f.len())
        .map(|&i| columns_ef[i - columns_f.len()])
        .collect::<Vec<_>>();

    let mut batched_column_down = if columns_shifted_f.is_empty() {
        tracing::warn!("TODO optimize open_columns when no shifted F columns");
        vec![EF::ZERO; batched_column_up.len()]
    } else {
        multilinears_linear_combination(
            columns_shifted_f,
            &eval_eq_batching_scalars[columns_f.len() + columns_ef.len()..]
                [..columns_shifted_f.len()],
        )
    };

    if !columns_shifted_ef.is_empty() {
        let batched_column_down_ef = multilinears_linear_combination(
            columns_shifted_ef,
            &eval_eq_batching_scalars
                [columns_f.len() + columns_ef.len() + columns_shifted_f.len()..],
        );
        batched_column_down
            .par_iter_mut()
            .zip(&batched_column_down_ef)
            .for_each(|(a, &b)| {
                *a += b;
            });
    }

    let sub_evals = info_span!("fold_multilinear_chunks").in_scope(|| {
        let sub_evals_up = fold_multilinear_chunks(
            &batched_column_up,
            &MultilinearPoint(outer_sumcheck_challenge[1..].to_vec()),
        );
        let sub_evals_down = fold_multilinear_chunks(
            &column_shifted(&batched_column_down, EF::ZERO),
            &MultilinearPoint(outer_sumcheck_challenge[1..].to_vec()),
        );
        sub_evals_up
            .iter()
            .zip(sub_evals_down.iter())
            .map(|(&up, &down)| up + down)
            .collect::<Vec<_>>()
    });
    prover_state.add_extension_scalars(&sub_evals);

    let epsilons = prover_state.sample_vec(univariate_skips);

    let inner_sum = sub_evals.evaluate(&MultilinearPoint(epsilons.clone()));

    let point = [epsilons, outer_sumcheck_challenge[1..].to_vec()].concat();

    // TODO opti in case of flat AIR (no need of `matrix_next_mle_folded`)
    let matrix_up = eval_eq(&point);
    let matrix_down = matrix_next_mle_folded(&point);
    let inner_mle = info_span!("packing").in_scope(|| {
        MleGroupOwned::ExtensionPacked(vec![
            pack_extension(&matrix_up),
            pack_extension(&batched_column_up),
            pack_extension(&matrix_down),
            pack_extension(&batched_column_down),
        ])
    });

    let (inner_challenges, _, _) = info_span!("structured columns sumcheck").in_scope(|| {
        sumcheck_prove::<EF, _, _>(
            1,
            inner_mle,
            None,
            &MySumcheck,
            &[],
            None,
            false,
            prover_state,
            inner_sum,
            false,
        )
    });

    let evaluations_remaining_to_prove = info_span!("final evals").in_scope(|| {
        let mut evals = columns_f
            .par_iter()
            .map(|col| col.evaluate(&inner_challenges))
            .collect::<Vec<_>>();
        evals.extend(
            columns_ef
                .par_iter()
                .map(|col| col.evaluate(&inner_challenges))
                .collect::<Vec<_>>(),
        );
        evals
    });
    prover_state.add_extension_scalars(&evaluations_remaining_to_prove);

    (inner_challenges, evaluations_remaining_to_prove)
}

struct MySumcheck;

impl<EF: ExtensionField<PF<EF>>> SumcheckComputation<EF> for MySumcheck {
    fn degree(&self) -> usize {
        2
    }
    #[inline(always)]
    fn eval_base(&self, _: &[PF<EF>], _: &[EF], _: &[EF]) -> EF {
        unreachable!()
    }
    #[inline(always)]
    fn eval_extension(&self, point: &[EF], _: &[EF], _: &[EF]) -> EF {
        point[0] * point[1] + point[2] * point[3]
    }
    #[inline(always)]
    fn eval_packed_base(
        &self,
        _: &[PFPacking<EF>],
        _: &[EFPacking<EF>],
        _: &[EF],
    ) -> EFPacking<EF> {
        unreachable!()
    }
    #[inline(always)]
    fn eval_packed_extension(
        &self,
        point: &[EFPacking<EF>],
        _: &[EFPacking<EF>],
        _: &[EF],
    ) -> EFPacking<EF> {
        point[0] * point[1] + point[2] * point[3]
    }
}
