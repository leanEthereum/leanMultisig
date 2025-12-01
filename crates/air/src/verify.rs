use multilinear_toolkit::prelude::*;
use p3_air::Air;
use p3_util::log2_ceil_usize;

use crate::utils::next_mle;

#[allow(clippy::type_complexity)]
#[allow(clippy::too_many_arguments)]
pub fn verify_air<EF: ExtensionField<PF<EF>>, A: Air>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    air: &A,
    extra_data: A::ExtraData,
    univariate_skips: usize,
    log_n_rows: usize,
    last_row_f: &[PF<EF>],
    last_row_ef: &[EF],
    virtual_column_statements: Option<(MultilinearPoint<EF>, Vec<Vec<EF>>)>, // point should be randomness generated after committing to the columns
) -> Result<(MultilinearPoint<EF>, Vec<EF>, Vec<EF>), ProofError> {
    let n_sc_rounds = log_n_rows + 1 - univariate_skips;

    let alpha = verifier_state.sample(); // random challenge for batching constraints
    let alpha_powers = alpha.powers().take(air.total_n_constraints()).collect();

    let virtual_column_statements = virtual_column_statements.unwrap_or_else(|| {
        let point = MultilinearPoint(verifier_state.sample_vec(n_sc_rounds));
        (point, vec![vec![]; <A as SumcheckComputation<EF>>::n_steps(air)])
    });

    let mut sum = EF::ZERO;
    assert_eq!(
        <A as SumcheckComputation<EF>>::n_steps(air),
        virtual_column_statements.1.len()
    );
    for (step, virtual_column_values) in virtual_column_statements.1.iter().enumerate() {
        sum += dot_product::<EF, _, _>(
            virtual_column_values.iter().copied(),
            alpha_powers[air.n_constraints_before_step(step)..].iter().copied(),
        );
    }

    let (sc_sum, outer_statement) = sumcheck_verify_with_univariate_skip::<EF>(
        verifier_state,
        <A as SumcheckComputation<EF>>::max_degree(air) + 1,
        log_n_rows,
        univariate_skips,
    )?;
    if sc_sum != sum {
        return Err(ProofError::InvalidProof);
    }

    let outer_selector_evals = univariate_selectors::<PF<EF>>(univariate_skips)
        .iter()
        .map(|s| s.evaluate(outer_statement.point[0]))
        .collect::<Vec<_>>();

    let mut inner_sums = verifier_state.next_extension_scalars_vec(
        air.n_columns_air() + air.down_column_indexes_f().len() + air.down_column_indexes_ef().len(),
    )?;

    let n_columns_down_f = air.down_column_indexes_f().len();
    let constraint_evals = SumcheckComputation::eval_extension_everywhere(
        air,
        &inner_sums[..air.n_columns_f_air() + n_columns_down_f],
        &inner_sums[air.n_columns_f_air() + n_columns_down_f..],
        &extra_data,
        &alpha_powers,
    );

    if eq_poly_with_skip(&virtual_column_statements.0, &outer_statement.point, univariate_skips) * constraint_evals
        != outer_statement.value
    {
        return Err(ProofError::InvalidProof);
    }

    inner_sums = [
        inner_sums[..air.n_columns_f_air()].to_vec(),
        inner_sums[air.n_columns_f_air() + n_columns_down_f..][..air.n_columns_ef_air()].to_vec(),
        inner_sums[air.n_columns_f_air()..][..n_columns_down_f].to_vec(),
        inner_sums[air.n_columns_f_air() + n_columns_down_f + air.n_columns_ef_air()..].to_vec(),
    ]
    .concat();

    open_columns(
        verifier_state,
        air.n_columns_f_air(),
        air.n_columns_ef_air(),
        univariate_skips,
        &air.down_column_indexes_f(),
        &air.down_column_indexes_ef(),
        inner_sums,
        &Evaluation::new(outer_statement.point[1..].to_vec(), outer_statement.value),
        &outer_selector_evals,
        log_n_rows,
        last_row_f,
        last_row_ef,
    )
}

#[allow(clippy::too_many_arguments)] // TODO
#[allow(clippy::type_complexity)]
fn open_columns<EF: ExtensionField<PF<EF>>>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    n_columns_f: usize,
    n_columns_ef: usize,
    univariate_skips: usize,
    columns_with_shift_f: &[usize],
    columns_with_shift_ef: &[usize],
    mut evals_up_and_down: Vec<EF>,
    outer_sumcheck_challenge: &Evaluation<EF>,
    outer_selector_evals: &[EF],
    log_n_rows: usize,
    last_row_f: &[PF<EF>],
    last_row_ef: &[EF],
) -> Result<(MultilinearPoint<EF>, Vec<EF>, Vec<EF>), ProofError> {
    let n_columns = n_columns_f + n_columns_ef;
    assert_eq!(
        n_columns + last_row_f.len() + last_row_ef.len(),
        evals_up_and_down.len()
    );
    let last_row_selector = outer_selector_evals[(1 << univariate_skips) - 1]
        * outer_sumcheck_challenge.point.iter().copied().product::<EF>();
    for (&last_row_value, down_col_eval) in last_row_f.iter().zip(&mut evals_up_and_down[n_columns..]) {
        *down_col_eval -= last_row_selector * last_row_value;
    }
    for (&last_row_value, down_col_eval) in last_row_ef
        .iter()
        .zip(&mut evals_up_and_down[n_columns + last_row_f.len()..])
    {
        *down_col_eval -= last_row_selector * last_row_value;
    }

    let batching_scalars = verifier_state.sample_vec(log2_ceil_usize(n_columns + last_row_f.len() + last_row_ef.len()));

    let eval_eq_batching_scalars = eval_eq(&batching_scalars);
    let batching_scalars_up = &eval_eq_batching_scalars[..n_columns];
    let batching_scalars_down = &eval_eq_batching_scalars[n_columns..];

    let sub_evals = verifier_state.next_extension_scalars_vec(1 << univariate_skips)?;

    if dot_product::<EF, _, _>(sub_evals.iter().copied(), outer_selector_evals.iter().copied())
        != dot_product::<EF, _, _>(
            evals_up_and_down.iter().copied(),
            eval_eq_batching_scalars.iter().copied(),
        )
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
    Ok((
        inner_sumcheck_stement.point.clone(),
        evaluations_remaining_to_verify_f,
        evaluations_remaining_to_verify_ef,
    ))
}
