use backend::*;
use lean_vm::EF;
use tracing::instrument;

use crate::*;

#[instrument(skip_all, fields(n_claims = statements.len(), n_vars = statements[0].total_num_variables))]
pub fn prove_reduction_many_sparse_claims_to_single_dense(
    prover_state: &mut impl FSProver<EF>,
    statements: &[SparseStatement<EF>],
    polynomial: &MleOwned<EF>,
) -> Evaluation<EF> {
    let n_vars = statements[0].total_num_variables;
    assert!(statements.iter().all(|s| s.total_num_variables == n_vars));

    let gamma: EF = prover_state.sample();
    let (weights, sum) = combine_sparse_statements(statements, gamma);
    let weights_mle = MleOwned::ExtensionPacked(weights);
    let packed_poly = polynomial.pack();
    let packed_poly_ref = packed_poly.by_ref();
    let weights_ref = weights_mle.by_ref();
    let (challenges, _final_sum, folded_poly, _folded_weights) =
        run_product_sumcheck(&packed_poly_ref, &weights_ref, prover_state, sum, n_vars, 0);

    let p_eval = folded_poly.evaluate(&MultilinearPoint(vec![]));

    Evaluation::new(challenges, p_eval)
}

pub fn verify_reduction_many_sparse_claims_to_single_dense(
    verifier_state: &mut impl FSVerifier<EF>,
    statements: &[SparseStatement<EF>],
) -> Result<Evaluation<EF>, ProofError> {
    let n_vars = statements[0].total_num_variables;
    assert!(statements.iter().all(|s| s.total_num_variables == n_vars));

    let gamma: EF = verifier_state.sample();

    let mut claimed_sum = EF::ZERO;
    let mut gamma_pow = EF::ONE;
    for smt in statements {
        for e in &smt.values {
            claimed_sum += gamma_pow * e.value;
            gamma_pow *= gamma;
        }
    }

    let Evaluation {
        point: challenges,
        value: final_claimed_sum,
    } = sumcheck_verify(verifier_state, n_vars, 2, claimed_sum, None)?;

    let w_eval = eval_combined_sparse_weights(statements, gamma, &challenges);
    let p_eval = final_claimed_sum / w_eval;

    Ok(Evaluation::new(challenges, p_eval))
}

fn eval_combined_sparse_weights(statements: &[SparseStatement<EF>], gamma: EF, point: &MultilinearPoint<EF>) -> EF {
    let mut value = EF::ZERO;
    let mut gamma_pow = EF::ONE;

    for smt in statements {
        let inner_eq = smt.point.eq_poly_outside(&MultilinearPoint(
            point[point.len() - smt.inner_num_variables()..].to_vec(),
        ));
        let sel_n_vars = smt.selector_num_variables();
        for e in &smt.values {
            let selector_eq: EF = (0..sel_n_vars)
                .map(|j| {
                    if e.selector & (1 << (sel_n_vars - 1 - j)) == 0 {
                        EF::ONE - point[j]
                    } else {
                        point[j]
                    }
                })
                .product();
            value += gamma_pow * selector_eq * inner_eq;
            gamma_pow *= gamma;
        }
    }

    value
}

#[instrument(skip_all, fields(num_constraints = statements.len(), n_vars = statements[0].total_num_variables))]
pub fn combine_sparse_statements<EF>(statements: &[SparseStatement<EF>], gamma: EF) -> (Vec<EFPacking<EF>>, EF)
where
    EF: ExtensionField<PF<EF>>,
{
    let num_variables = statements[0].total_num_variables;
    assert!(statements.iter().all(|e| e.total_num_variables == num_variables));

    let mut combined_weights = EFPacking::<EF>::zero_vec(1 << (num_variables - packing_log_width::<EF>()));

    let mut combined_sum = EF::ZERO;
    let mut gamma_pow = EF::ONE;

    for smt in statements {
        if smt.values.len() == 1 || smt.inner_num_variables() < packing_log_width::<EF>() {
            for evaluation in &smt.values {
                compute_sparse_eval_eq_packed::<EF>(evaluation.selector, &smt.point, &mut combined_weights, gamma_pow);
                combined_sum += evaluation.value * gamma_pow;
                gamma_pow *= gamma;
            }
        } else {
            let poly_eq = eval_eq_packed(&smt.point);
            let shift = smt.inner_num_variables() - packing_log_width::<EF>();
            let mut indexed_smt_values = smt.values.iter().enumerate().collect::<Vec<_>>();
            indexed_smt_values.sort_by_key(|(_, e)| e.selector);
            indexed_smt_values.dedup_by_key(|(_, e)| e.selector);
            assert_eq!(
                indexed_smt_values.len(),
                smt.values.len(),
                "Duplicate selectors in sparse statement"
            );
            let mut chunks_mut = split_at_mut_many(
                &mut combined_weights,
                &indexed_smt_values
                    .iter()
                    .map(|(_, e)| e.selector << shift)
                    .collect::<Vec<_>>(),
            );
            chunks_mut.remove(0);
            let mut next_gamma_powers = vec![gamma_pow];
            for _ in 1..indexed_smt_values.len() {
                next_gamma_powers.push(*next_gamma_powers.last().unwrap() * gamma);
            }
            for (e, &scalar) in smt.values.iter().zip(&next_gamma_powers) {
                combined_sum += e.value * scalar;
            }
            chunks_mut
                .into_par_iter()
                .zip(&indexed_smt_values)
                .for_each(|(out_buff, &(origin_index, _))| {
                    out_buff[..1 << shift]
                        .par_iter_mut()
                        .zip(&poly_eq)
                        .for_each(|(out_elem, &poly_eq_elem)| {
                            *out_elem += poly_eq_elem * next_gamma_powers[origin_index];
                        });
                });
            gamma_pow = *next_gamma_powers.last().unwrap() * gamma;
        }
    }

    (combined_weights, combined_sum)
}
