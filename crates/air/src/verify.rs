use backend::*;

use crate::AirClaims;

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

    let expected_sum = virtual_column_statement.as_ref().map(|st| st.value).unwrap_or(EF::ZERO);
    let outer_statement = sumcheck_verify(
        verifier_state,
        log_n_rows,
        air.degree_air() + 1, // +1 for the eq factor
        expected_sum,
        Some(&zerocheck_challenges),
    )?;

    let inner_evals = verifier_state.next_extension_scalars_vec(air.n_columns() + air.n_down_columns())?;

    let n_columns_down = air.n_down_columns();
    let constraint_evals = air.eval_extension(&inner_evals[..air.n_columns() + n_columns_down], &extra_data);

    if MultilinearPoint(zerocheck_challenges.clone()).eq_poly_outside(&outer_statement.point) * constraint_evals
        != outer_statement.value
    {
        return Err(ProofError::InvalidProof);
    }

    let n_columns_up = air.n_columns();
    let n_columns_down = air.n_down_columns();
    assert_eq!(inner_evals.len(), n_columns_up + n_columns_down);

    Ok(AirClaims {
        point: outer_statement.point,
        evals: inner_evals[..n_columns_up].to_vec(),
        evals_down: inner_evals[n_columns_up..].to_vec(),
    })
}
