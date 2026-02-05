use multilinear_toolkit::prelude::*;
use p3_util::{log2_ceil_usize, log2_strict_usize};
use tracing::{info_span, instrument};
use utils::{fold_multilinear_chunks, multilinears_linear_combination};

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
    univariate_skips: usize,
    columns_f: &[impl AsRef<[PF<EF>]>],
    columns_ef: &[impl AsRef<[EF]>],
    virtual_column_statement: Option<Evaluation<EF>>, // point should be randomness generated after committing to the columns
    store_intermediate_foldings: bool,
) -> AirClaims<EF>
where
    A::ExtraData: AlphaPowersMut<EF> + AlphaPowers<EF>,
{
    let columns_f: Vec<_> = columns_f.iter().map(|c| c.as_ref()).collect();
    let columns_ef: Vec<_> = columns_ef.iter().map(|c| c.as_ref()).collect();
    let n_rows = columns_f[0].len();
    assert!(columns_f.iter().all(|col| col.len() == n_rows));
    assert!(columns_ef.iter().all(|col| col.len() == n_rows));
    let log_n_rows = log2_strict_usize(n_rows);
    assert!(
        univariate_skips < log_n_rows,
        "TODO handle the case UNIVARIATE_SKIPS >= log_length"
    );

    // crate::check_air_validity(air, &extra_data, &columns_f, &columns_ef).unwrap();

    assert!(extra_data.alpha_powers().len() >= air.n_constraints() + virtual_column_statement.is_some() as usize);

    let n_sc_rounds = log_n_rows + 1 - univariate_skips;

    let zerocheck_challenges = virtual_column_statement
        .as_ref()
        .map(|st| st.point.0.clone())
        .unwrap_or_else(|| prover_state.sample_vec(n_sc_rounds));
    assert_eq!(zerocheck_challenges.len(), n_sc_rounds);

    let shifted_rows_f = air
        .down_column_indexes_f()
        .par_iter()
        .map(|&col_index| column_shifted(columns_f[col_index]))
        .collect::<Vec<_>>();
    let shifted_rows_ef = air
        .down_column_indexes_ef()
        .par_iter()
        .map(|&col_index| column_shifted(columns_ef[col_index]))
        .collect::<Vec<_>>();

    let mut columns_up_down_f = columns_f.to_vec(); // orginal columns, followed by shifted ones
    columns_up_down_f.extend(shifted_rows_f.iter().map(Vec::as_slice));

    let mut columns_up_down_ef = columns_ef.to_vec(); // orginal columns, followed by shifted ones
    columns_up_down_ef.extend(shifted_rows_ef.iter().map(Vec::as_slice));

    let columns_up_down_group_f: MleGroupRef<'_, EF> = MleGroupRef::<'_, EF>::Base(columns_up_down_f);
    let columns_up_down_group_ef: MleGroupRef<'_, EF> = MleGroupRef::<'_, EF>::Extension(columns_up_down_ef);

    let columns_up_down_group_f_packed = columns_up_down_group_f.pack();
    let columns_up_down_group_ef_packed = columns_up_down_group_ef.pack();

    let (outer_sumcheck_challenge, inner_sums, _) = info_span!("zerocheck").in_scope(|| {
        sumcheck_prove(
            univariate_skips,
            columns_up_down_group_f_packed,
            Some(columns_up_down_group_ef_packed),
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

    if univariate_skips == 1 {
        open_columns_no_skip(
            prover_state,
            &inner_sums,
            &air.down_column_indexes_f(),
            &air.down_column_indexes_ef(),
            &columns_f,
            &columns_ef,
            &outer_sumcheck_challenge,
        )
    } else if shifted_rows_f.is_empty() && shifted_rows_ef.is_empty() {
        // usefull for poseidon2 benchmark
        open_flat_columns(
            prover_state,
            univariate_skips,
            &columns_f,
            &columns_ef,
            &outer_sumcheck_challenge,
        )
    } else {
        panic!(
            "Currently unsupported for simplicty (checkout c7944152a4325b1e1913446e6684112099db5d78 for a version that supported this case)"
        );
    }
}

#[instrument(skip_all)]
fn open_flat_columns<EF: ExtensionField<PF<EF>>>(
    prover_state: &mut impl FSProver<EF>,
    univariate_skips: usize,
    columns_f: &[&[PF<EF>]],
    columns_ef: &[&[EF]],
    outer_sumcheck_challenge: &[EF],
) -> AirClaims<EF> {
    let n_up_down_columns = columns_f.len() + columns_ef.len();
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

    let sub_evals = fold_multilinear_chunks(
        &batched_column_up,
        &MultilinearPoint(outer_sumcheck_challenge[1..].to_vec()),
    );
    prover_state.add_extension_scalars(&sub_evals);

    let epsilons = prover_state.sample_vec(univariate_skips);

    let inner_sum = sub_evals.evaluate(&MultilinearPoint(epsilons.clone()));

    let point = [epsilons, outer_sumcheck_challenge[1..].to_vec()].concat();

    // TODO opti in case of flat AIR (no need of `matrix_next_mle_folded`)
    let matrix_up = eval_eq(&point);
    let inner_mle = info_span!("packing").in_scope(|| {
        MleGroupOwned::ExtensionPacked(vec![pack_extension(&matrix_up), pack_extension(&batched_column_up)])
    });

    let (inner_challenges, _, _) = info_span!("structured columns sumcheck").in_scope(|| {
        sumcheck_prove::<EF, _, _>(
            1,
            inner_mle,
            None,
            &ProductComputation {},
            &vec![],
            None,
            false,
            prover_state,
            inner_sum,
            false,
        )
    });

    let (evaluations_remaining_to_prove_f, evaluations_remaining_to_prove_ef) =
        info_span!("final evals").in_scope(|| {
            (
                columns_f
                    .par_iter()
                    .map(|col| col.evaluate(&inner_challenges))
                    .collect::<Vec<_>>(),
                columns_ef
                    .par_iter()
                    .map(|col| col.evaluate(&inner_challenges))
                    .collect::<Vec<_>>(),
            )
        });
    prover_state.add_extension_scalars(&evaluations_remaining_to_prove_f);
    prover_state.add_extension_scalars(&evaluations_remaining_to_prove_ef);

    AirClaims {
        point: inner_challenges,
        evals_f: evaluations_remaining_to_prove_f,
        evals_ef: evaluations_remaining_to_prove_ef,
        down_point: None,
        evals_f_on_down_columns: vec![],
        evals_ef_on_down_columns: vec![],
    }
}

#[instrument(skip_all)]
fn open_columns_no_skip<EF: ExtensionField<PF<EF>>>(
    prover_state: &mut impl FSProver<EF>,
    inner_evals: &[EF],
    columns_with_shift_f: &[usize],
    columns_with_shift_ef: &[usize],
    columns_f: &[&[PF<EF>]],
    columns_ef: &[&[EF]],
    outer_sumcheck_challenge: &[EF],
) -> AirClaims<EF> {
    let n_columns_f_up = columns_f.len();
    let n_columns_ef_up = columns_ef.len();
    let n_columns_f_down = columns_with_shift_f.len();
    let n_columns_ef_down = columns_with_shift_ef.len();
    let n_down_columns = n_columns_f_down + n_columns_ef_down;
    assert_eq!(inner_evals.len(), n_columns_f_up + n_columns_ef_up + n_down_columns);

    let evals_up_f = inner_evals[..n_columns_f_up].to_vec();
    let evals_down_f = &inner_evals[n_columns_f_up..][..n_columns_f_down];
    let evals_up_ef = inner_evals[n_columns_f_up + n_columns_f_down..][..n_columns_ef_up].to_vec();
    let evals_down_ef = &inner_evals[n_columns_f_up + n_columns_f_down + n_columns_ef_up..];

    if n_down_columns == 0 {
        return AirClaims {
            point: MultilinearPoint(outer_sumcheck_challenge.to_vec()),
            evals_f: evals_up_f,
            evals_ef: evals_up_ef,
            down_point: None,
            evals_f_on_down_columns: vec![],
            evals_ef_on_down_columns: vec![],
        };
    }

    let batching_scalar = prover_state.sample();
    let batching_scalar_powers = batching_scalar.powers().collect_n(n_down_columns);

    let columns_shifted_f = &columns_with_shift_f.iter().map(|&i| columns_f[i]).collect::<Vec<_>>();
    let columns_shifted_ef = &columns_with_shift_ef.iter().map(|&i| columns_ef[i]).collect::<Vec<_>>();

    let mut batched_column_down =
        multilinears_linear_combination(columns_shifted_f, &batching_scalar_powers[..n_columns_f_down]);

    if n_columns_ef_down > 0 {
        let batched_column_down_ef =
            multilinears_linear_combination(columns_shifted_ef, &batching_scalar_powers[n_columns_f_down..]);
        batched_column_down
            .par_iter_mut()
            .zip(&batched_column_down_ef)
            .for_each(|(a, &b)| {
                *a += b;
            });
    }

    let matrix_down = matrix_next_mle_folded(outer_sumcheck_challenge);
    let inner_mle = info_span!("packing").in_scope(|| {
        MleGroupOwned::ExtensionPacked(vec![pack_extension(&matrix_down), pack_extension(&batched_column_down)])
    });

    let inner_sum = dot_product(
        evals_down_f.iter().chain(evals_down_ef).copied(),
        batching_scalar_powers.iter().copied(),
    );

    let (inner_challenges, _, _) = info_span!("structured columns sumcheck").in_scope(|| {
        sumcheck_prove::<EF, _, _>(
            1,
            inner_mle,
            None,
            &ProductComputation {},
            &vec![],
            None,
            false,
            prover_state,
            inner_sum,
            false,
        )
    });

    let (evals_f_on_down_columns, evals_ef_on_down_columns) = info_span!("final evals").in_scope(|| {
        (
            columns_shifted_f
                .par_iter()
                .map(|col| col.evaluate(&inner_challenges))
                .collect::<Vec<_>>(),
            columns_shifted_ef
                .par_iter()
                .map(|col| col.evaluate(&inner_challenges))
                .collect::<Vec<_>>(),
        )
    });
    prover_state.add_extension_scalars(&evals_f_on_down_columns);
    prover_state.add_extension_scalars(&evals_ef_on_down_columns);

    AirClaims {
        point: MultilinearPoint(outer_sumcheck_challenge.to_vec()),
        evals_f: evals_up_f,
        evals_ef: evals_up_ef,
        down_point: Some(inner_challenges),
        evals_f_on_down_columns,
        evals_ef_on_down_columns,
    }
}
