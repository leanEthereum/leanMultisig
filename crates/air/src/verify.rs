use backend::*;

use crate::{AirClaims, utils::next_mle};

#[allow(clippy::type_complexity)]
#[allow(clippy::too_many_arguments)]
pub fn verify_air<EF: ExtensionField<PF<EF>>, A: Air>(
    verifier_state: &mut impl FSVerifier<EF>,
    air: &A,
    extra_data: A::ExtraData,
    log_n_rows: usize,
    virtual_column_statement: Option<Evaluation<EF>>, // point should be randomness generated after committing to the columns
) -> ProofResult<AirClaims<EF>>
where
    A::ExtraData: AlphaPowersMut<EF> + AlphaPowers<EF>,
{
    assert!(extra_data.alpha_powers().len() >= air.n_constraints() + virtual_column_statement.is_some() as usize);

    let zerocheck_challenges = virtual_column_statement
        .as_ref()
        .map(|st| st.point.0.clone())
        .unwrap_or_else(|| verifier_state.sample_vec(log_n_rows));
    assert_eq!(zerocheck_challenges.len(), log_n_rows);

    let (sc_sum, outer_statement) = sumcheck_verify::<EF>(verifier_state, log_n_rows, air.degree_air() + 1)?;
    if sc_sum
        != virtual_column_statement
            .as_ref()
            .map(|st| st.value)
            .unwrap_or_else(|| EF::ZERO)
    {
        return Err(ProofError::InvalidProof);
    }

    let inner_evals = verifier_state
        .next_extension_scalars_vec(air.n_columns_air() + air.n_down_columns_f() + air.n_down_columns_ef())?;

    let n_columns_down_f = air.n_down_columns_f();
    let constraint_evals = air.eval_extension(
        &inner_evals[..air.n_columns_f_air() + n_columns_down_f],
        &inner_evals[air.n_columns_f_air() + n_columns_down_f..],
        &extra_data,
    );

    if MultilinearPoint(zerocheck_challenges.clone()).eq_poly_outside(&outer_statement.point) * constraint_evals
        != outer_statement.value
    {
        return Err(ProofError::InvalidProof);
    }

    open_columns(verifier_state, air, log_n_rows, &inner_evals, &outer_statement.point)
}

fn open_columns<A: Air, EF: ExtensionField<PF<EF>>>(
    verifier_state: &mut impl FSVerifier<EF>,
    air: &A,
    log_n_rows: usize,
    inner_evals: &[EF],
    outer_sumcheck_challenge: &[EF],
) -> ProofResult<AirClaims<EF>> {
    let n_columns_f_up = air.n_columns_f_air();
    let n_columns_ef_up = air.n_columns_ef_air();
    let n_columns_f_down = air.n_down_columns_f();
    let n_columns_ef_down = air.n_down_columns_ef();
    let n_down_columns = n_columns_f_down + n_columns_ef_down;
    assert_eq!(inner_evals.len(), n_columns_f_up + n_columns_ef_up + n_down_columns);

    let evals_up_f = inner_evals[..n_columns_f_up].to_vec();
    let evals_down_f = inner_evals[n_columns_f_up..][..n_columns_f_down].to_vec();
    let evals_up_ef = inner_evals[n_columns_f_up + n_columns_f_down..][..n_columns_ef_up].to_vec();
    let evals_down_ef = inner_evals[n_columns_f_up + n_columns_f_down + n_columns_ef_up..].to_vec();

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

    let batching_scalar = verifier_state.sample();
    let batching_scalar_powers = batching_scalar.powers().collect_n(n_down_columns);

    let inner_sum: EF = dot_product(
        evals_down_f.into_iter().chain(evals_down_ef),
        batching_scalar_powers.iter().copied(),
    );

    let (inner_sum_retrieved, inner_sumcheck_stement) = sumcheck_verify(verifier_state, log_n_rows, 2)?;

    if inner_sum != inner_sum_retrieved {
        return Err(ProofError::InvalidProof);
    }

    let matrix_down_sc_eval = next_mle(outer_sumcheck_challenge, &inner_sumcheck_stement.point);

    let evals_f_on_down_columns = verifier_state.next_extension_scalars_vec(n_columns_f_down)?;
    let evals_ef_on_down_columns = verifier_state.next_extension_scalars_vec(n_columns_ef_down)?;
    let evaluations_remaining_to_verify = [evals_f_on_down_columns.clone(), evals_ef_on_down_columns.clone()].concat();
    let batched_col_down_sc_eval = dot_product::<EF, _, _>(
        batching_scalar_powers.iter().copied(),
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
