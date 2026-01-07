use multilinear_toolkit::prelude::*;
use p3_util::log2_ceil_usize;

use crate::{AirClaims, utils::next_mle};

#[allow(clippy::type_complexity)]
#[allow(clippy::too_many_arguments)]
pub fn verify_air<EF: ExtensionField<PF<EF>>, A: Air>(
    verifier_state: &mut impl FSVerifier<EF>,
    air: &A,
    extra_data: A::ExtraData,
    univariate_skips: usize,
    log_n_rows: usize,
    virtual_column_statement: Option<Evaluation<EF>>, // point should be randomness generated after committing to the columns
) -> ProofResult<AirClaims<EF>>
where
    A::ExtraData: AlphaPowersMut<EF> + AlphaPowers<EF>,
{
    assert!(extra_data.alpha_powers().len() >= air.n_constraints() + virtual_column_statement.is_some() as usize);

    let n_sc_rounds = log_n_rows + 1 - univariate_skips;
    let zerocheck_challenges = virtual_column_statement
        .as_ref()
        .map(|st| st.point.0.clone())
        .unwrap_or_else(|| verifier_state.sample_vec(n_sc_rounds));
    assert_eq!(zerocheck_challenges.len(), n_sc_rounds);

    let (sc_sum, outer_statement) =
        sumcheck_verify_with_univariate_skip::<EF>(verifier_state, air.degree_air() + 1, log_n_rows, univariate_skips)?;
    if sc_sum
        != virtual_column_statement
            .as_ref()
            .map(|st| st.value)
            .unwrap_or_else(|| EF::ZERO)
    {
        return Err(ProofError::InvalidProof);
    }

    let outer_selector_evals = univariate_selectors::<PF<EF>>(univariate_skips)
        .iter()
        .map(|s| s.evaluate(outer_statement.point[0]))
        .collect::<Vec<_>>();

    let mut inner_evals = verifier_state.next_extension_scalars_vec(
        air.n_columns_air() + air.down_column_indexes_f().len() + air.down_column_indexes_ef().len(),
    )?;

    let n_columns_down_f = air.down_column_indexes_f().len();
    let constraint_evals = SumcheckComputation::eval_extension(
        air,
        &inner_evals[..air.n_columns_f_air() + n_columns_down_f],
        &inner_evals[air.n_columns_f_air() + n_columns_down_f..],
        &extra_data,
    );

    if eq_poly_with_skip(&zerocheck_challenges, &outer_statement.point, univariate_skips) * constraint_evals
        != outer_statement.value
    {
        return Err(ProofError::InvalidProof);
    }

    inner_evals = [
        inner_evals[..air.n_columns_f_air()].to_vec(),
        inner_evals[air.n_columns_f_air() + n_columns_down_f..][..air.n_columns_ef_air()].to_vec(),
        inner_evals[air.n_columns_f_air()..][..n_columns_down_f].to_vec(),
        inner_evals[air.n_columns_f_air() + n_columns_down_f + air.n_columns_ef_air()..].to_vec(),
    ]
    .concat();

    if univariate_skips == 1 {
        open_columns_no_skip(verifier_state, air, log_n_rows, &inner_evals, &outer_statement.point)
    } else {
        open_columns(
            verifier_state,
            air.n_columns_f_air(),
            air.n_columns_ef_air(),
            univariate_skips,
            &air.down_column_indexes_f(),
            &air.down_column_indexes_ef(),
            inner_evals,
            &Evaluation::new(outer_statement.point[1..].to_vec(), outer_statement.value),
            &outer_selector_evals,
            log_n_rows,
        )
    }
}

#[allow(clippy::too_many_arguments)] // TODO
#[allow(clippy::type_complexity)]
fn open_columns<EF: ExtensionField<PF<EF>>>(
    verifier_state: &mut impl FSVerifier<EF>,
    n_columns_f: usize,
    n_columns_ef: usize,
    univariate_skips: usize,
    columns_with_shift_f: &[usize],
    columns_with_shift_ef: &[usize],
    inner_evals: Vec<EF>,
    outer_sumcheck_challenge: &Evaluation<EF>,
    outer_selector_evals: &[EF],
    log_n_rows: usize,
) -> ProofResult<AirClaims<EF>> {
    let n_columns = n_columns_f + n_columns_ef;

    let batching_scalars = verifier_state.sample_vec(log2_ceil_usize(
        n_columns + columns_with_shift_f.len() + columns_with_shift_ef.len(),
    ));

    let eval_eq_batching_scalars = eval_eq(&batching_scalars);
    let batching_scalars_up = &eval_eq_batching_scalars[..n_columns];
    let batching_scalars_down = &eval_eq_batching_scalars[n_columns..];

    let sub_evals = verifier_state.next_extension_scalars_vec(1 << univariate_skips)?;

    if dot_product::<EF, _, _>(sub_evals.iter().copied(), outer_selector_evals.iter().copied())
        != dot_product::<EF, _, _>(inner_evals.iter().copied(), eval_eq_batching_scalars.iter().copied())
    {
        return Err(ProofError::InvalidProof);
    }

    let epsilons = MultilinearPoint(verifier_state.sample_vec(univariate_skips));

    let (inner_sum, inner_sumcheck_stement) = sumcheck_verify(verifier_state, log_n_rows, 2)?;

    if inner_sum != sub_evals.evaluate(&epsilons) {
        return Err(ProofError::InvalidProof);
    }

    let matrix_up_sc_eval = MultilinearPoint([epsilons.0.clone(), outer_sumcheck_challenge.point.0.clone()].concat())
        .eq_poly_outside(&inner_sumcheck_stement.point);
    let matrix_down_sc_eval = next_mle(
        &[
            epsilons.0,
            outer_sumcheck_challenge.point.to_vec(),
            inner_sumcheck_stement.point.0.clone(),
        ]
        .concat(),
    );

    let evaluations_remaining_to_verify_f = verifier_state.next_extension_scalars_vec(n_columns_f)?;
    let evaluations_remaining_to_verify_ef = verifier_state.next_extension_scalars_vec(n_columns_ef)?;
    let evaluations_remaining_to_verify = [
        evaluations_remaining_to_verify_f.clone(),
        evaluations_remaining_to_verify_ef.clone(),
    ]
    .concat();
    let batched_col_up_sc_eval = dot_product::<EF, _, _>(
        batching_scalars_up.iter().copied(),
        evaluations_remaining_to_verify.iter().copied(),
    );
    let mut columns_with_shift = columns_with_shift_f.to_vec();
    columns_with_shift.extend_from_slice(
        columns_with_shift_ef
            .iter()
            .map(|&x| x + n_columns_f)
            .collect::<Vec<_>>()
            .as_slice(),
    );
    let batched_col_down_sc_eval = (0..columns_with_shift.len())
        .map(|i| evaluations_remaining_to_verify[columns_with_shift[i]] * batching_scalars_down[i])
        .sum::<EF>();

    if inner_sumcheck_stement.value
        != matrix_up_sc_eval * batched_col_up_sc_eval + matrix_down_sc_eval * batched_col_down_sc_eval
    {
        return Err(ProofError::InvalidProof);
    }
    Ok(AirClaims {
        point: inner_sumcheck_stement.point.clone(),
        evals_f: evaluations_remaining_to_verify_f,
        evals_ef: evaluations_remaining_to_verify_ef,
        down_point: None,
        evals_f_on_down_columns: vec![],
        evals_ef_on_down_columns: vec![],
    })
}

fn open_columns_no_skip<A: Air, EF: ExtensionField<PF<EF>>>(
    verifier_state: &mut impl FSVerifier<EF>,
    air: &A,
    log_n_rows: usize,
    inner_evals: &[EF],
    outer_sumcheck_challenge: &[EF],
) -> ProofResult<AirClaims<EF>> {
    let n_columns_f_up = air.n_columns_f_air();
    let n_columns_ef_up = air.n_columns_ef_air();
    let n_columns_f_down = air.down_column_indexes_f().len();
    let n_columns_ef_down = air.down_column_indexes_ef().len();
    let n_up_columns = n_columns_f_up + n_columns_ef_up;
    let n_down_columns = n_columns_f_down + n_columns_ef_down;
    assert_eq!(inner_evals.len(), n_columns_f_up + n_columns_ef_up + n_down_columns);

    let evls_up = &inner_evals[..n_up_columns];
    let evals_down = &inner_evals[n_up_columns..];
    let evals_up_f = evls_up[..n_columns_f_up].to_vec();
    let evals_up_ef = evls_up[n_columns_f_up..].to_vec();

    if n_down_columns == 0 {
        return Ok(AirClaims {
            point: MultilinearPoint(outer_sumcheck_challenge.to_vec()),
            evals_f: evals_up_f,
            evals_ef: evals_up_ef,
            down_point: None,
            evals_f_on_down_columns: vec![],
            evals_ef_on_down_columns: vec![],
        });
    }

    let batching_scalars = verifier_state.sample_vec(log2_ceil_usize(n_down_columns));
    let eval_eq_batching_scalars = eval_eq(&batching_scalars)[..n_down_columns].to_vec();

    let inner_sum: EF = dot_product(evals_down.iter().copied(), eval_eq_batching_scalars.iter().copied());

    let (inner_sum_retrieved, inner_sumcheck_stement) = sumcheck_verify(verifier_state, log_n_rows, 2)?;

    if inner_sum != inner_sum_retrieved {
        return Err(ProofError::InvalidProof);
    }

    let matrix_down_sc_eval = next_mle(
        &[
            outer_sumcheck_challenge.to_vec(),
            inner_sumcheck_stement.point.0.clone(),
        ]
        .concat(),
    );

    let evals_f_on_down_columns = verifier_state.next_extension_scalars_vec(n_columns_f_down)?;
    let evals_ef_on_down_columns = verifier_state.next_extension_scalars_vec(n_columns_ef_down)?;
    let evaluations_remaining_to_verify = [evals_f_on_down_columns.clone(), evals_ef_on_down_columns.clone()].concat();
    let batched_col_down_sc_eval = dot_product::<EF, _, _>(
        eval_eq_batching_scalars.iter().copied(),
        evaluations_remaining_to_verify.iter().copied(),
    );

    if inner_sumcheck_stement.value != matrix_down_sc_eval * batched_col_down_sc_eval {
        return Err(ProofError::InvalidProof);
    }

    Ok(AirClaims {
        point: MultilinearPoint(outer_sumcheck_challenge.to_vec()),
        evals_f: evals_up_f,
        evals_ef: evals_up_ef,
        down_point: Some(inner_sumcheck_stement.point.clone()),
        evals_f_on_down_columns,
        evals_ef_on_down_columns,
    })
}
