use multilinear_toolkit::prelude::*;
use p3_koala_bear::{KoalaBearInternalLayerParameters, KoalaBearParameters};
use p3_monty_31::InternalLayerBaseParameters;

use crate::{EF, gkr_layers::PoseidonGKRLayers};

pub fn verify_poseidon_gkr<const WIDTH: usize, const N_COMMITED_CUBES: usize>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    log_n_poseidons: usize,
    output_claim_point: &[EF],
    layers: &PoseidonGKRLayers<WIDTH, N_COMMITED_CUBES>,
    univariate_skips: usize,
) -> ((Vec<EF>, Vec<EF>), (Vec<EF>, Vec<EF>))
where
    KoalaBearInternalLayerParameters: InternalLayerBaseParameters<KoalaBearParameters, WIDTH>,
{
    let mut output_claims = verifier_state.next_extension_scalars_vec(WIDTH).unwrap();

    let mut claim_point = output_claim_point.to_vec();
    for full_round in layers.final_full_rounds.iter().rev() {
        (claim_point, output_claims) = verify_gkr_round(
            verifier_state,
            full_round,
            log_n_poseidons,
            &claim_point,
            &output_claims,
            univariate_skips,
        );
    }

    for partial_round in layers.partial_rounds_remaining.iter().rev() {
        (claim_point, output_claims) = verify_gkr_round(
            verifier_state,
            partial_round,
            log_n_poseidons,
            &claim_point,
            &output_claims,
            univariate_skips,
        );
    }
    let claimed_cubes_evals = verifier_state
        .next_extension_scalars_vec(N_COMMITED_CUBES)
        .unwrap();

    (claim_point, output_claims) = verify_gkr_round(
        verifier_state,
        &layers.batch_partial_rounds,
        log_n_poseidons,
        &claim_point,
        &[output_claims, claimed_cubes_evals.clone()].concat(),
        univariate_skips,
    );

    let pcs_point_for_cubes = claim_point.clone();
    let pcs_evals_for_cubes = output_claims[WIDTH..].to_vec();

    output_claims = output_claims[..WIDTH].to_vec();

    for full_round in layers.initial_full_rounds_remaining.iter().rev() {
        (claim_point, output_claims) = verify_gkr_round(
            verifier_state,
            full_round,
            log_n_poseidons,
            &claim_point,
            &output_claims,
            univariate_skips,
        );
    }
    (claim_point, output_claims) = verify_gkr_round(
        verifier_state,
        &layers.initial_full_round,
        log_n_poseidons,
        &claim_point,
        &output_claims,
        univariate_skips,
    );

    let pcs_point_for_inputs = claim_point.clone();
    let pcs_evals_for_inputs = output_claims.to_vec();

    (
        (pcs_point_for_inputs, pcs_evals_for_inputs),
        (pcs_point_for_cubes, pcs_evals_for_cubes),
    )
}

fn verify_gkr_round<SC: SumcheckComputation<EF, EF>>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    computation: &SC,
    log_n_poseidons: usize,
    claim_point: &[EF],
    output_claims: &[EF],
    univariate_skips: usize,
) -> (Vec<EF>, Vec<EF>) {
    let batching_scalar = verifier_state.sample();
    let batching_scalars_powers = batching_scalar.powers().collect_n(output_claims.len());
    let batched_claim: EF = dot_product(output_claims.iter().copied(), batching_scalar.powers());

    let (retrieved_batched_claim, sumcheck_postponed_claim) = sumcheck_verify_with_univariate_skip(
        verifier_state,
        computation.degree() + 1,
        log_n_poseidons,
        univariate_skips,
    )
    .unwrap();

    assert_eq!(retrieved_batched_claim, batched_claim);

    let sumcheck_inner_evals = verifier_state
        .next_extension_scalars_vec(output_claims.len())
        .unwrap();
    assert_eq!(
        computation.eval(&sumcheck_inner_evals, &batching_scalars_powers)
            * eq_poly_with_skip(
                &sumcheck_postponed_claim.point,
                &claim_point,
                univariate_skips
            ),
        sumcheck_postponed_claim.value
    );

    (sumcheck_postponed_claim.point.0, sumcheck_inner_evals)
}
