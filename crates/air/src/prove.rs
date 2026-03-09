use backend::*;
use tracing::{info_span, instrument};
use utils::multilinears_linear_combination;

use crate::{AirClaims, uni_skip_utils::matrix_next_mle_folded, utils::column_shifted};

/*

cf https://eprint.iacr.org/2023/552.pdf and https://solvable.group/posts/super-air/#fnref:1

*/

#[instrument(name = "prove air", skip_all)]
#[allow(clippy::too_many_arguments)]
pub fn prove_air<EF: ExtensionField<PF<EF>>, A: Air>(
    prover_state: &mut impl FSProver<EF>,
    air: &A,
    extra_data: A::ExtraData,
    columns: &[impl AsRef<[PF<EF>]>],
    virtual_column_statement: Option<Evaluation<EF>>, // point should be randomness generated after committing to the columns
    store_intermediate_foldings: bool,
) -> AirClaims<EF>
where
    A::ExtraData: AlphaPowersMut<EF> + AlphaPowers<EF>,
{
    let columns: Vec<_> = columns.iter().map(|c| c.as_ref()).collect();
    let n_rows = columns[0].len();
    assert!(columns.iter().all(|col| col.len() == n_rows));
    let log_n_rows = log2_strict_usize(n_rows);

    assert!(extra_data.alpha_powers().len() >= air.n_constraints() + virtual_column_statement.is_some() as usize);

    let zerocheck_challenges = virtual_column_statement
        .as_ref()
        .map(|st| st.point.0.clone())
        .unwrap_or_else(|| prover_state.sample_vec(log_n_rows));
    assert_eq!(zerocheck_challenges.len(), log_n_rows);

    let shifted_rows = air
        .down_column_indexes()
        .par_iter()
        .map(|&col_index| column_shifted(columns[col_index]))
        .collect::<Vec<_>>();

    let mut columns_up_down = columns.to_vec(); // orginal columns, followed by shifted ones
    columns_up_down.extend(shifted_rows.iter().map(Vec::as_slice));

    let columns_up_down_group: MleGroupRef<'_, EF> = MleGroupRef::<'_, EF>::Base(columns_up_down);

    let columns_up_down_group_packed = columns_up_down_group.pack();

    let (outer_sumcheck_challenge, inner_sums, _) = info_span!("zerocheck").in_scope(|| {
        sumcheck_prove(
            columns_up_down_group_packed,
            air,
            &extra_data,
            Some((zerocheck_challenges, None)),
            virtual_column_statement.is_none(),
            prover_state,
            virtual_column_statement
                .as_ref()
                .map(|st| st.value)
                .unwrap_or_else(|| EF::ZERO),
            store_intermediate_foldings,
        )
    });

    prover_state.add_extension_scalars(&inner_sums);

    open_columns(
        prover_state,
        &inner_sums,
        &air.down_column_indexes(),
        &columns,
        &outer_sumcheck_challenge,
    )
}

#[instrument(skip_all)]
fn open_columns<EF: ExtensionField<PF<EF>>>(
    prover_state: &mut impl FSProver<EF>,
    inner_evals: &[EF],
    columns_with_shift: &[usize],
    columns: &[&[PF<EF>]],
    outer_sumcheck_challenge: &[EF],
) -> AirClaims<EF> {
    let n_columns_up = columns.len();
    let n_columns_down = columns_with_shift.len();
    assert_eq!(inner_evals.len(), n_columns_up + n_columns_down);

    let evals_up = inner_evals[..n_columns_up].to_vec();
    let evals_down = &inner_evals[n_columns_up..];

    if n_columns_down == 0 {
        return AirClaims {
            point: MultilinearPoint(outer_sumcheck_challenge.to_vec()),
            evals: evals_up,
            down_point: None,
            evals_on_down_columns: vec![],
        };
    }

    let batching_scalar = prover_state.sample();
    let batching_scalar_powers = batching_scalar.powers().collect_n(n_columns_down);

    let columns_shifted = &columns_with_shift.iter().map(|&i| columns[i]).collect::<Vec<_>>();

    let batched_column_down = multilinears_linear_combination(columns_shifted, &batching_scalar_powers);

    let matrix_down = matrix_next_mle_folded(outer_sumcheck_challenge);
    let inner_mle = info_span!("packing").in_scope(|| {
        MleGroupOwned::ExtensionPacked(vec![pack_extension(&matrix_down), pack_extension(&batched_column_down)])
    });

    let inner_sum = dot_product(evals_down.iter().copied(), batching_scalar_powers.iter().copied());

    let (inner_challenges, _, _) = info_span!("structured columns sumcheck").in_scope(|| {
        sumcheck_prove::<EF, _, _>(
            inner_mle,
            &ProductComputation {},
            &vec![],
            None,
            false,
            prover_state,
            inner_sum,
            false,
        )
    });

    let evals_on_down_columns = info_span!("final evals").in_scope(|| {
        columns_shifted
            .par_iter()
            .map(|col| col.evaluate(&inner_challenges))
            .collect::<Vec<_>>()
    });
    prover_state.add_extension_scalars(&evals_on_down_columns);

    AirClaims {
        point: MultilinearPoint(outer_sumcheck_challenge.to_vec()),
        evals: evals_up,
        down_point: Some(inner_challenges),
        evals_on_down_columns,
    }
}
