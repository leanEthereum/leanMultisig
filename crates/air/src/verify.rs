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

    let inner_evals = verifier_state.next_extension_scalars_vec(air.n_columns() + air.n_down_columns())?;

    let n_columns_down = air.n_down_columns();
    let constraint_evals = air.eval_extension(&inner_evals[..air.n_columns() + n_columns_down], &extra_data);

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
    let n_columns_up = air.n_columns();
    let n_columns_down = air.n_down_columns();
    assert_eq!(inner_evals.len(), n_columns_up + n_columns_down);

    let evals_up = inner_evals[..n_columns_up].to_vec();
    let evals_down = inner_evals[n_columns_up..].to_vec();

    if n_columns_down == 0 {
        return Ok(AirClaims {
            point: MultilinearPoint(outer_sumcheck_challenge.to_vec()),
            evals: evals_up,
            down_point: None,
            evals_on_down_columns: vec![],
        });
    }

    let batching_scalar = verifier_state.sample();
    let batching_scalar_powers = batching_scalar.powers().collect_n(n_columns_down);

    let inner_sum: EF = dot_product(evals_down.into_iter(), batching_scalar_powers.iter().copied());

    let (inner_sum_retrieved, inner_sumcheck_stement) = sumcheck_verify(verifier_state, log_n_rows, 2)?;

    if inner_sum != inner_sum_retrieved {
        return Err(ProofError::InvalidProof);
    }

    let matrix_down_sc_eval = next_mle(outer_sumcheck_challenge, &inner_sumcheck_stement.point);

    let evals_on_down_columns = verifier_state.next_extension_scalars_vec(n_columns_down)?;
    let batched_col_down_sc_eval = dot_product::<EF, _, _>(
        batching_scalar_powers.iter().copied(),
        evals_on_down_columns.iter().copied(),
    );

    if inner_sumcheck_stement.value != matrix_down_sc_eval * batched_col_down_sc_eval {
        return Err(ProofError::InvalidProof);
    }

    Ok(AirClaims {
        point: MultilinearPoint(outer_sumcheck_challenge.to_vec()),
        evals: evals_up,
        down_point: Some(inner_sumcheck_stement.point.clone()),
        evals_on_down_columns,
    })
}
