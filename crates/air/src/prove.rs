use backend::*;
use tracing::{info_span, instrument};

use crate::AirClaims;

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
            Some(zerocheck_challenges),
            prover_state,
            virtual_column_statement
                .as_ref()
                .map(|st| st.value)
                .unwrap_or_else(|| EF::ZERO),
            store_intermediate_foldings,
        )
    });

    prover_state.add_extension_scalars(&inner_sums);

    AirClaims {
        point: MultilinearPoint(outer_sumcheck_challenge.to_vec()),
        evals: inner_sums[..columns.len()].to_vec(),
        evals_down: inner_sums[columns.len()..].to_vec(),
    }
}

pub(crate) fn column_shifted<F: Field>(column: &[F]) -> Vec<F> {
    let mut down = unsafe { uninitialized_vec(column.len()) };
    parallel_clone(&column[1..], &mut down[..column.len() - 1]);
    down[column.len() - 1] = column[column.len() - 1];
    down
}
