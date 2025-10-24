use crate::{
    EF, F, PoseidonWitness,
    gkr_layers::{BatchPartialRounds, PoseidonGKRLayers},
};
use multilinear_toolkit::prelude::*;
use p3_koala_bear::{KoalaBearInternalLayerParameters, KoalaBearParameters};
use p3_monty_31::InternalLayerBaseParameters;
use tracing::{info_span, instrument};

pub fn prove_poseidon_gkr<const WIDTH: usize, const N_COMMITED_CUBES: usize>(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    witness: &PoseidonWitness<FPacking<F>, WIDTH, N_COMMITED_CUBES>,
    mut claim_point: Vec<EF>,
    univariate_skips: usize,
    layers: &PoseidonGKRLayers<WIDTH, N_COMMITED_CUBES>,
) -> (Vec<EF>, Vec<EF>)
where
    KoalaBearInternalLayerParameters: InternalLayerBaseParameters<KoalaBearParameters, WIDTH>,
{
    let selectors = univariate_selectors::<F>(univariate_skips);

    let mut output_claims = info_span!("computing output claims").in_scope(|| {
        batch_evaluate_univariate_multilinear(
            &witness
                .output_layer
                .iter()
                .map(|l| PFPacking::<EF>::unpack_slice(l))
                .collect::<Vec<_>>(),
            &claim_point,
            &selectors,
        )
    });

    prover_state.add_extension_scalars(&output_claims);

    for (input_layers, full_round) in witness
        .final_full_round_inputs
        .iter()
        .zip(&layers.final_full_rounds)
        .rev()
    {
        (claim_point, output_claims) = prove_gkr_round(
            prover_state,
            full_round,
            input_layers,
            &claim_point,
            &output_claims,
            univariate_skips,
        );
    }

    for (input_layers, partial_round) in witness
        .remaining_partial_round_inputs
        .iter()
        .zip(&layers.partial_rounds_remaining)
        .rev()
    {
        (claim_point, output_claims) = prove_gkr_round(
            prover_state,
            partial_round,
            input_layers,
            &claim_point,
            &output_claims,
            univariate_skips,
        );
    }

    (claim_point, output_claims) = prove_batch_internal_round(
        prover_state,
        &witness.batch_partial_round_input,
        &witness.committed_cubes,
        &layers.batch_partial_rounds,
        &claim_point,
        &output_claims,
        &selectors,
    );

    let pcs_point_for_cubes = claim_point.clone();

    output_claims = output_claims[..WIDTH].to_vec();

    for (input_layers, full_round) in witness
        .remaining_initial_full_round_inputs
        .iter()
        .zip(&layers.initial_full_rounds_remaining)
        .rev()
    {
        (claim_point, output_claims) = prove_gkr_round(
            prover_state,
            full_round,
            input_layers,
            &claim_point,
            &output_claims,
            univariate_skips,
        );
    }
    (claim_point, _) = prove_gkr_round(
        prover_state,
        &layers.initial_full_round,
        &witness.input_layer,
        &claim_point,
        &output_claims,
        univariate_skips,
    );
    let pcs_point_for_inputs = claim_point.clone();

    (pcs_point_for_inputs, pcs_point_for_cubes)
}

#[instrument(skip_all)]
fn prove_gkr_round<
    SC: SumcheckComputation<F, EF>
        + SumcheckComputation<EF, EF>
        + SumcheckComputationPacked<EF>
        + 'static,
>(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    computation: &SC,
    input_layers: &[impl AsRef<Vec<PFPacking<EF>>>],
    claim_point: &[EF],
    output_claims: &[EF],
    univariate_skips: usize,
) -> (Vec<EF>, Vec<EF>) {
    let batching_scalar = prover_state.sample();
    let batching_scalars_powers = batching_scalar.powers().collect_n(output_claims.len());
    let batched_claim: EF = dot_product(
        output_claims.iter().copied(),
        batching_scalars_powers.iter().copied(),
    );

    let (sumcheck_point, sumcheck_inner_evals, sumcheck_final_sum) = sumcheck_prove(
        univariate_skips,
        MleGroupRef::BasePacked(input_layers.iter().map(|l| l.as_ref().as_slice()).collect()),
        computation,
        computation,
        &batching_scalars_powers,
        Some((claim_point.to_vec(), None)),
        false,
        prover_state,
        batched_claim,
        None,
    );

    // sanity check
    debug_assert_eq!(
        computation.eval(&sumcheck_inner_evals, &batching_scalars_powers)
            * eq_poly_with_skip(&sumcheck_point, &claim_point, univariate_skips),
        sumcheck_final_sum
    );

    prover_state.add_extension_scalars(&sumcheck_inner_evals);

    (sumcheck_point.0, sumcheck_inner_evals)
}

#[instrument(skip_all)]
fn prove_batch_internal_round<const WIDTH: usize, const N_COMMITED_CUBES: usize>(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    input_layers: &[Vec<PFPacking<EF>>],
    committed_cubes: &[Vec<PFPacking<EF>>],
    computation: &BatchPartialRounds<WIDTH, N_COMMITED_CUBES>,
    claim_point: &[EF],
    output_claims: &[EF],
    selectors: &[DensePolynomial<F>],
) -> (Vec<EF>, Vec<EF>)
where
    KoalaBearInternalLayerParameters: InternalLayerBaseParameters<KoalaBearParameters, WIDTH>,
{
    assert_eq!(input_layers.len(), WIDTH);
    assert_eq!(committed_cubes.len(), N_COMMITED_CUBES);
    let univariate_skips = log2_strict_usize(selectors.len());

    let cubes_evals = info_span!("computing cube evals").in_scope(|| {
        batch_evaluate_univariate_multilinear(
            &committed_cubes
                .iter()
                .map(|l| PFPacking::<EF>::unpack_slice(l))
                .collect::<Vec<_>>(),
            &claim_point,
            selectors,
        )
    });

    prover_state.add_extension_scalars(&cubes_evals);

    let batching_scalar = prover_state.sample();
    let batched_claim: EF = dot_product(
        output_claims.iter().chain(&cubes_evals).copied(),
        batching_scalar.powers(),
    );
    let batching_scalars_powers = batching_scalar.powers().collect_n(WIDTH + N_COMMITED_CUBES);

    let (sumcheck_point, sumcheck_inner_evals, sumcheck_final_sum) = sumcheck_prove(
        univariate_skips,
        MleGroupRef::BasePacked(
            input_layers
                .iter()
                .chain(committed_cubes.iter())
                .map(Vec::as_slice)
                .collect(),
        ),
        computation,
        computation,
        &batching_scalars_powers,
        Some((claim_point.to_vec(), None)),
        false,
        prover_state,
        batched_claim,
        None,
    );

    // sanity check
    debug_assert_eq!(
        computation.eval(&sumcheck_inner_evals, &batching_scalars_powers)
            * eq_poly_with_skip(&sumcheck_point, &claim_point, univariate_skips),
        sumcheck_final_sum
    );

    prover_state.add_extension_scalars(&sumcheck_inner_evals);

    (sumcheck_point.0, sumcheck_inner_evals)
}
