use multilinear_toolkit::prelude::*;
use p3_air::BaseAir;
use p3_util::log2_ceil_usize;

use crate::{MyAir, utils::next_mle};

use super::table::AirTable;

pub fn verify_air<EF: ExtensionField<PF<EF>>, A: MyAir<EF>>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    table: &AirTable<EF, A>,
    univariate_skips: usize,
    log_n_rows: usize,
    last_row: &[EF],
    virtual_column_statement: Option<Evaluation<EF>>, // point should be randomness generated after committing to the columns
) -> Result<(MultilinearPoint<EF>, Vec<EF>), ProofError> {
    let constraints_batching_scalar = verifier_state.sample();

    let n_sc_rounds = log_n_rows + 1 - univariate_skips;
    let zerocheck_challenges = virtual_column_statement
        .as_ref()
        .map(|st| st.point.0.clone())
        .unwrap_or_else(|| verifier_state.sample_vec(n_sc_rounds));
    assert_eq!(zerocheck_challenges.len(), n_sc_rounds);

    let (sc_sum, outer_statement) = sumcheck_verify_with_univariate_skip::<EF>(
        verifier_state,
        <A as BaseAir<PF<EF>>>::degree(&table.air) + 1,
        log_n_rows,
        univariate_skips,
    )?;
    if sc_sum
        != virtual_column_statement
            .as_ref()
            .map(|st| st.value)
            .unwrap_or(EF::ZERO)
    {
        return Err(ProofError::InvalidProof);
    }

    let outer_selector_evals = univariate_selectors::<PF<EF>>(univariate_skips)
        .iter()
        .map(|s| s.evaluate(outer_statement.point[0]))
        .collect::<Vec<_>>();

    let inner_sums = verifier_state
        .next_extension_scalars_vec(table.n_columns() + table.columns_with_shift().len())?;

    let constraints_batching_scalars = constraints_batching_scalar
        .powers()
        .take(table.n_constraints + virtual_column_statement.is_some() as usize)
        .collect();
    let constraint_evals =
        SumcheckComputation::eval::<EF>(&table.air, &inner_sums, &constraints_batching_scalars);

    if eq_poly_with_skip(
        &zerocheck_challenges,
        &outer_statement.point,
        univariate_skips,
    ) * constraint_evals
        != outer_statement.value
    {
        return Err(ProofError::InvalidProof);
    }

    open_columns(
        verifier_state,
        table.n_columns(),
        univariate_skips,
        &table.columns_with_shift(),
        inner_sums,
        &Evaluation::new(outer_statement.point[1..].to_vec(), outer_statement.value),
        &outer_selector_evals,
        log_n_rows,
        last_row,
    )
}

#[allow(clippy::too_many_arguments)] // TODO
fn open_columns<EF: ExtensionField<PF<EF>>>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    n_columns: usize,
    univariate_skips: usize,
    columns_with_shift: &[usize],
    mut evals_up_and_down: Vec<EF>,
    outer_sumcheck_challenge: &Evaluation<EF>,
    outer_selector_evals: &[EF],
    log_n_rows: usize,
    last_row: &[EF],
) -> Result<(MultilinearPoint<EF>, Vec<EF>), ProofError> {
    assert_eq!(n_columns + last_row.len(), evals_up_and_down.len());
    let last_row_selector = outer_selector_evals[(1 << univariate_skips) - 1]
        * outer_sumcheck_challenge
            .point
            .iter()
            .copied()
            .product::<EF>();
    for (&last_row_value, down_col_eval) in last_row.iter().zip(&mut evals_up_and_down[n_columns..])
    {
        *down_col_eval -= last_row_value * last_row_selector;
    }

    let batching_scalars = verifier_state.sample_vec(log2_ceil_usize(n_columns + last_row.len()));

    let eval_eq_batching_scalars = eval_eq(&batching_scalars);
    let batching_scalars_up = &eval_eq_batching_scalars[..n_columns];
    let batching_scalars_down = &eval_eq_batching_scalars[n_columns..];

    let sub_evals = verifier_state.next_extension_scalars_vec(1 << univariate_skips)?;

    if dot_product::<EF, _, _>(
        sub_evals.iter().copied(),
        outer_selector_evals.iter().copied(),
    ) != dot_product::<EF, _, _>(
        evals_up_and_down.iter().copied(),
        eval_eq_batching_scalars.iter().copied(),
    ) {
        return Err(ProofError::InvalidProof);
    }

    let epsilons = MultilinearPoint(verifier_state.sample_vec(univariate_skips));

    let (inner_sum, inner_sumcheck_stement) = sumcheck_verify(verifier_state, log_n_rows, 2)?;

    if inner_sum != sub_evals.evaluate(&epsilons) {
        return Err(ProofError::InvalidProof);
    }

    let matrix_up_sc_eval =
        MultilinearPoint([epsilons.0.clone(), outer_sumcheck_challenge.point.0.clone()].concat())
            .eq_poly_outside(&inner_sumcheck_stement.point);
    let matrix_down_sc_eval = next_mle(
        &[
            epsilons.0,
            outer_sumcheck_challenge.point.to_vec(),
            inner_sumcheck_stement.point.0.clone(),
        ]
        .concat(),
    );

    let evaluations_remaining_to_verify = verifier_state.next_extension_scalars_vec(n_columns)?;

    let batched_col_up_sc_eval = dot_product::<EF, _, _>(
        batching_scalars_up.iter().copied(),
        evaluations_remaining_to_verify.iter().copied(),
    );
    let batched_col_down_sc_eval = (0..columns_with_shift.len())
        .map(|i| evaluations_remaining_to_verify[columns_with_shift[i]] * batching_scalars_down[i])
        .sum::<EF>();

    if inner_sumcheck_stement.value
        != matrix_up_sc_eval * batched_col_up_sc_eval
            + matrix_down_sc_eval * batched_col_down_sc_eval
    {
        return Err(ProofError::InvalidProof);
    }
    Ok((
        inner_sumcheck_stement.point.clone(),
        evaluations_remaining_to_verify,
    ))
}
