use std::any::TypeId;

use multilinear_toolkit::prelude::*;
use p3_util::{log2_ceil_usize, log2_strict_usize};
use tracing::{info_span, instrument};
use utils::{FSProver, fold_multilinear_chunks, multilinears_linear_combination};

use crate::MyAir;
use crate::{uni_skip_utils::matrix_next_mle_folded, utils::column_shifted};

use super::table::AirTable;

/*

cf https://eprint.iacr.org/2023/552.pdf and https://solvable.group/posts/super-air/#fnref:1

*/

#[instrument(name = "prove air", skip_all)]
pub fn prove_air<
    WF: ExtensionField<PF<EF>>, // witness field
    EF: ExtensionField<PF<EF>> + ExtensionField<WF>,
    A: MyAir<EF> + 'static,
>(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    table: &AirTable<EF, A>,
    univariate_skips: usize,
    witness: &[&[WF]],
    last_row_shifted: &[WF],
    virtual_column_statement: Option<Evaluation<EF>>, // point should be randomness generated after committing to the columns
) -> (MultilinearPoint<EF>, Vec<EF>) {
    let n_rows = witness[0].len();
    assert!(witness.iter().all(|col| col.len() == n_rows));
    let log_n_rows = log2_strict_usize(n_rows);
    assert!(
        univariate_skips < log_n_rows,
        "TODO handle the case UNIVARIATE_SKIPS >= log_length"
    );

    let constraints_batching_scalar = prover_state.sample();

    let constraints_batching_scalars = constraints_batching_scalar
        .powers()
        .take(table.n_constraints + virtual_column_statement.is_some() as usize)
        .collect();

    let n_sc_rounds = log_n_rows + 1 - univariate_skips;

    let zerocheck_challenges = virtual_column_statement
        .as_ref()
        .map(|st| st.point.0.clone())
        .unwrap_or_else(|| prover_state.sample_vec(n_sc_rounds));
    assert_eq!(zerocheck_challenges.len(), n_sc_rounds);

    let shifted_rows = table
        .columns_with_shift()
        .par_iter()
        .zip_eq(last_row_shifted)
        .map(|(&col_index, &final_value)| column_shifted(witness[col_index], final_value))
        .collect::<Vec<_>>();

    let mut columns_up_down = witness.to_vec(); // orginal columns, followed by shifted ones
    columns_up_down.extend(shifted_rows.iter().map(Vec::as_slice));
    let columns_up_down_group: MleGroupRef<'_, EF> = if TypeId::of::<WF>() == TypeId::of::<PF<EF>>()
    {
        let columns =
            unsafe { std::mem::transmute::<Vec<&[WF]>, Vec<&[PF<EF>]>>(columns_up_down.clone()) };
        MleGroupRef::<'_, EF>::Base(columns)
    } else {
        assert!(TypeId::of::<WF>() == TypeId::of::<EF>());
        let columns =
            unsafe { std::mem::transmute::<Vec<&[WF]>, Vec<&[EF]>>(columns_up_down.clone()) };
        MleGroupRef::<'_, EF>::Extension(columns)
    };

    let columns_up_down_packed = columns_up_down_group.pack();

    let (outer_sumcheck_challenge, inner_sums, _) = info_span!("zerocheck").in_scope(|| {
        sumcheck_prove(
            univariate_skips,
            columns_up_down_packed,
            &table.air,
            &constraints_batching_scalars,
            Some((zerocheck_challenges, None)),
            virtual_column_statement.is_none(),
            prover_state,
            virtual_column_statement
                .as_ref()
                .map(|st| st.value)
                .unwrap_or_else(|| EF::ZERO),
            None,
        )
    });

    prover_state.add_extension_scalars(&inner_sums);

    open_columns(
        prover_state,
        univariate_skips,
        &table.columns_with_shift(),
        witness,
        &outer_sumcheck_challenge,
    )
}

#[instrument(skip_all)]
fn open_columns<EF: ExtensionField<PF<EF>> + ExtensionField<IF>, IF: Field>(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    univariate_skips: usize,
    columns_with_shift: &[usize],
    columns: &[&[IF]],
    outer_sumcheck_challenge: &[EF],
) -> (MultilinearPoint<EF>, Vec<EF>) {
    let n_up_down_columns = columns.len() + columns_with_shift.len();
    let batching_scalars = prover_state.sample_vec(log2_ceil_usize(n_up_down_columns));

    let eval_eq_batching_scalars = eval_eq(&batching_scalars)[..n_up_down_columns].to_vec();

    let batched_column_up =
        multilinears_linear_combination(columns, &eval_eq_batching_scalars[..columns.len()]);
    let batched_column_down = multilinears_linear_combination(
        &columns_with_shift
            .iter()
            .map(|&i| columns[i])
            .collect::<Vec<_>>(),
        &eval_eq_batching_scalars[columns.len()..],
    );

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
            &MySumcheck,
            &[],
            None,
            false,
            prover_state,
            inner_sum,
            None,
        )
    });

    let evaluations_remaining_to_prove = info_span!("final evals").in_scope(|| {
        columns
            .par_iter()
            .map(|col| col.evaluate(&inner_challenges))
            .collect::<Vec<_>>()
    });
    prover_state.add_extension_scalars(&evaluations_remaining_to_prove);

    (inner_challenges, evaluations_remaining_to_prove)
}

struct MySumcheck;

impl<IF: ExtensionField<PF<EF>>, EF: ExtensionField<IF>> SumcheckComputation<IF, EF>
    for MySumcheck
{
    fn eval(&self, point: &[IF], _: &[EF]) -> EF {
        if TypeId::of::<IF>() == TypeId::of::<EF>() {
            let point = unsafe { std::mem::transmute::<&[IF], &[EF]>(point) };
            point[0] * point[1] + point[2] * point[3]
        } else {
            unreachable!()
        }
    }
    fn degree(&self) -> usize {
        2
    }
}

impl<EF: ExtensionField<PF<EF>>> SumcheckComputationPacked<EF> for MySumcheck {
    fn eval_packed_base(&self, _: &[PFPacking<EF>], _: &[EF]) -> EFPacking<EF> {
        unreachable!()
    }
    fn eval_packed_extension(&self, point: &[EFPacking<EF>], _: &[EF]) -> EFPacking<EF> {
        point[0] * point[1] + point[2] * point[3]
    }
    fn degree(&self) -> usize {
        2
    }
}
