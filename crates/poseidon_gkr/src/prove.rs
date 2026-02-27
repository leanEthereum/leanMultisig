use crate::{
    EF, F, FullRoundComputation, GKRPoseidonResult, POSEIDON_16_GKR_START, POSEIDON_16_N_GKR_COLS,
    PartialRoundComputation, apply_matrix, build_poseidon_inv_matrices, poseidon_round_constants,
};
use backend::*;
use tracing::{info_span, instrument};

#[instrument(skip_all)]
pub fn prove_poseidon_gkr<const WIDTH: usize>(
    prover_state: &mut impl FSProver<EF>,
    trace: &[Vec<F>],
    output_point: MultilinearPoint<EF>,
    perm_out_0_7: &[EF],
) -> GKRPoseidonResult
where
    KoalaBearInternalLayerParameters: InternalLayerBaseParameters<KoalaBearParameters, WIDTH>,
{
    let (inv_external_matrix, inv_internal_matrix) = build_poseidon_inv_matrices::<WIDTH>();
    let (initial_constants, internal_constants, final_constants) = poseidon_round_constants::<WIDTH>();

    let n_poseidons = trace[0].len();
    assert_eq!(output_point.0.len(), log2_strict_usize(n_poseidons));
    assert_eq!(perm_out_0_7.len(), WIDTH / 2);

    let n_initial = initial_constants.len();
    let n_partial = internal_constants.len();
    let n_final = final_constants.len();

    // Layer offsets in the trace
    let initial_start = POSEIDON_16_GKR_START;
    let partial_start = initial_start + n_initial * WIDTH;
    let final_start = partial_start + n_partial * WIDTH;
    let output_layer_start = final_start + n_final * WIDTH;
    assert_eq!(
        output_layer_start + WIDTH,
        POSEIDON_16_GKR_START + POSEIDON_16_N_GKR_COLS
    );

    let perm_out_8_15: Vec<EF> = info_span!("computing perm_out[8..15]").in_scope(|| {
        (WIDTH / 2..WIDTH)
            .into_par_iter()
            .map(|col| (&trace[output_layer_start + col][..]).evaluate(&output_point))
            .collect()
    });
    prover_state.add_extension_scalars(&perm_out_8_15);

    let mut point = output_point.0.clone();
    let mut claims: Vec<EF> = [perm_out_0_7, &perm_out_8_15].concat();

    //final full rounds
    for (idx, full_round_constants) in final_constants.iter().enumerate().rev() {
        claims = apply_matrix(&inv_external_matrix, &claims);

        let layer_base = final_start + idx * WIDTH;
        let layer_slices: Vec<&[FPacking<F>]> = (0..WIDTH)
            .map(|j| FPacking::<F>::pack_slice(&trace[layer_base + j]))
            .collect();
        (point, claims) = prove_gkr_round(prover_state, &FullRoundComputation {}, &layer_slices, &point, &claims);

        for (claim, c) in claims.iter_mut().zip(full_round_constants) {
            *claim -= *c;
        }
    }

    // partial rounds
    for (idx, partial_round_constant) in internal_constants.iter().enumerate().rev() {
        claims = apply_matrix(&inv_internal_matrix, &claims);

        let layer_base = partial_start + idx * WIDTH;
        let layer_slices: Vec<&[FPacking<F>]> = (0..WIDTH)
            .map(|j| FPacking::<F>::pack_slice(&trace[layer_base + j]))
            .collect();
        (point, claims) = prove_gkr_round(
            prover_state,
            &PartialRoundComputation::<WIDTH> {},
            &layer_slices,
            &point,
            &claims,
        );
        claims[0] -= *partial_round_constant;
    }

    // initial full rounds
    for (idx, full_round_constants) in initial_constants.iter().enumerate().rev() {
        claims = apply_matrix(&inv_external_matrix, &claims);

        let layer_base = initial_start + idx * WIDTH;
        let layer_slices: Vec<&[FPacking<F>]> = (0..WIDTH)
            .map(|j| FPacking::<F>::pack_slice(&trace[layer_base + j]))
            .collect();
        (point, claims) = prove_gkr_round(prover_state, &FullRoundComputation {}, &layer_slices, &point, &claims);

        for (claim, c) in claims.iter_mut().zip(full_round_constants) {
            *claim -= *c;
        }
    }

    claims = apply_matrix(&inv_external_matrix, &claims);

    GKRPoseidonResult {
        input_point: MultilinearPoint(point),
        input_evals: claims,
    }
}

fn prove_gkr_round<SC: SumcheckComputation<EF, ExtraData = Vec<EF>> + 'static>(
    prover_state: &mut impl FSProver<EF>,
    computation: &SC,
    input_layers: &[&[PFPacking<EF>]],
    claim_point: &[EF],
    output_claims: &[EF],
) -> (Vec<EF>, Vec<EF>) {
    let batching_scalar = prover_state.sample();
    let batching_scalars_powers: Vec<EF> = batching_scalar.powers().collect_n(output_claims.len());
    let batched_claim: EF = dot_product(output_claims.iter().copied(), batching_scalars_powers.iter().copied());

    let (sumcheck_point, sumcheck_inner_evals, sumcheck_final_sum) = sumcheck_prove(
        MleGroupRef::BasePacked(input_layers.to_vec()),
        computation,
        &batching_scalars_powers,
        Some((claim_point.to_vec(), None)),
        false,
        prover_state,
        batched_claim,
        true,
    );

    // sanity check
    debug_assert_eq!(
        computation.eval_extension(&sumcheck_inner_evals, &batching_scalars_powers)
            * sumcheck_point.eq_poly_outside(&MultilinearPoint(claim_point.to_vec())),
        sumcheck_final_sum
    );

    prover_state.add_extension_scalars(&sumcheck_inner_evals);

    (sumcheck_point.0, sumcheck_inner_evals)
}
