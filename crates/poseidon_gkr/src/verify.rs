use backend::*;

use crate::{
    EF, FullRoundComputation, GKRPoseidonResult, PartialRoundComputation, apply_matrix, build_poseidon_inv_matrices,
    poseidon_round_constants,
};

pub fn verify_poseidon_gkr<const WIDTH: usize>(
    verifier_state: &mut impl FSVerifier<EF>,
    log_n_poseidons: usize,
    output_claim_point: &MultilinearPoint<EF>,
    perm_out_0_7: &[EF],
) -> Result<GKRPoseidonResult, ProofError>
where
    KoalaBearInternalLayerParameters: InternalLayerBaseParameters<KoalaBearParameters, WIDTH>,
{
    let (inv_external_matrix, inv_internal_matrix) = build_poseidon_inv_matrices::<WIDTH>();
    let (initial_constants, internal_constants, final_constants) = poseidon_round_constants::<WIDTH>();

    assert_eq!(perm_out_0_7.len(), WIDTH / 2);

    // Receive perm_out[8..15] from prover
    let perm_out_8_15 = verifier_state.next_extension_scalars_vec(WIDTH / 2)?;

    let mut point = output_claim_point.0.clone();
    let mut claims: Vec<EF> = [perm_out_0_7, &perm_out_8_15].concat();
    assert_eq!(claims.len(), WIDTH);

    // final full rounds
    for full_round_constants in final_constants.iter().rev() {
        claims = apply_matrix(&inv_external_matrix, &claims);

        (point, claims) = verify_gkr_round(
            verifier_state,
            &FullRoundComputation {},
            log_n_poseidons,
            &point,
            &claims,
            WIDTH,
        )?;

        for (claim, c) in claims.iter_mut().zip(full_round_constants) {
            *claim -= *c;
        }
    }

    // partial rounds
    for partial_round_constant in internal_constants.iter().rev() {
        claims = apply_matrix(&inv_internal_matrix, &claims);

        (point, claims) = verify_gkr_round(
            verifier_state,
            &PartialRoundComputation::<WIDTH> {},
            log_n_poseidons,
            &point,
            &claims,
            WIDTH,
        )?;

        claims[0] -= *partial_round_constant;
    }

    // initial full rounds
    for full_round_constants in initial_constants.iter().rev() {
        claims = apply_matrix(&inv_external_matrix, &claims);

        (point, claims) = verify_gkr_round(
            verifier_state,
            &FullRoundComputation {},
            log_n_poseidons,
            &point,
            &claims,
            WIDTH,
        )?;

        for (claim, c) in claims.iter_mut().zip(full_round_constants) {
            *claim -= *c;
        }
    }

    claims = apply_matrix(&inv_external_matrix, &claims);

    Ok(GKRPoseidonResult {
        input_point: MultilinearPoint(point),
        input_evals: claims,
    })
}

fn verify_gkr_round<SC: SumcheckComputation<EF, ExtraData = Vec<EF>>>(
    verifier_state: &mut impl FSVerifier<EF>,
    computation: &SC,
    log_n_poseidons: usize,
    claim_point: &[EF],
    output_claims: &[EF],
    n_inputs: usize,
) -> Result<(Vec<EF>, Vec<EF>), ProofError> {
    let batching_scalar = verifier_state.sample();
    let batching_scalars_powers: Vec<EF> = batching_scalar.powers().collect_n(output_claims.len());
    let batched_claim: EF = dot_product(output_claims.iter().copied(), batching_scalar.powers());

    let (retrieved_batched_claim, sumcheck_postponed_claim) =
        sumcheck_verify(verifier_state, log_n_poseidons, computation.degree() + 1)?;

    if retrieved_batched_claim != batched_claim {
        return Err(ProofError::InvalidProof);
    }

    let sumcheck_inner_evals = verifier_state.next_extension_scalars_vec(n_inputs)?;
    let expected = computation.eval_extension(&sumcheck_inner_evals, &batching_scalars_powers)
        * sumcheck_postponed_claim
            .point
            .eq_poly_outside(&MultilinearPoint(claim_point.to_vec()));
    if expected != sumcheck_postponed_claim.value {
        return Err(ProofError::InvalidProof);
    }

    Ok((sumcheck_postponed_claim.point.0, sumcheck_inner_evals))
}
