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
) -> (
    [EF; WIDTH],
    (MultilinearPoint<EF>, Vec<EF>),
    (MultilinearPoint<EF>, Vec<EF>),
)
where
    KoalaBearInternalLayerParameters: InternalLayerBaseParameters<KoalaBearParameters, WIDTH>,
{
    let selectors = univariate_selectors::<F>(univariate_skips);

    assert_eq!(claim_point.len(), log2_strict_usize(witness.n_poseidons()));

    let (output_claims, mut claims) = info_span!("computing output claims").in_scope(|| {
        let eq_poly = eval_eq(&claim_point[univariate_skips..]);
        let inner_evals = witness
            .output_layer
            .par_iter()
            .map(|poly| {
                FPacking::<F>::unpack_slice(poly)
                    .chunks_exact(eq_poly.len())
                    .map(|chunk| dot_product(eq_poly.iter().copied(), chunk.iter().copied()))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        for evals in &inner_evals {
            prover_state.add_extension_scalars(evals);
        }
        let alpha = prover_state.sample();
        claim_point = [vec![alpha], claim_point[univariate_skips..].to_vec()].concat();
        let selectors_at_alpha = selectors
            .iter()
            .map(|selector| selector.evaluate(alpha))
            .collect::<Vec<_>>();

        let mut output_claims = vec![];
        let mut claims = vec![];
        for evals in inner_evals {
            output_claims
                .push(evals.evaluate(&MultilinearPoint(claim_point[..univariate_skips].to_vec())));
            claims.push(dot_product(
                selectors_at_alpha.iter().copied(),
                evals.into_iter(),
            ))
        }
        (output_claims, claims)
    });

    for (i, (input_layers, full_round)) in witness
        .final_full_round_inputs
        .iter()
        .zip(&layers.final_full_rounds)
        .rev()
        .enumerate()
    {
        let mut input_layers = input_layers.iter().map(Vec::as_slice).collect::<Vec<_>>();
        if i == 0
            && let Some((_, compression_indicator)) = &witness.compression
        {
            input_layers.push(compression_indicator);
        }
        (claim_point, claims) = prove_gkr_round(
            prover_state,
            full_round,
            &input_layers,
            &claim_point,
            &claims,
            univariate_skips,
        );

        if i == 0 && witness.compression.is_some() {
            let _ = claims.pop().unwrap(); // the claim on the compression indicator columns can be evaluated by the verifier directly
        }
    }

    for (input_layers, partial_round) in witness
        .remaining_partial_round_inputs
        .iter()
        .zip(&layers.partial_rounds_remaining)
        .rev()
    {
        (claim_point, claims) = prove_gkr_round(
            prover_state,
            partial_round,
            input_layers,
            &claim_point,
            &claims,
            univariate_skips,
        );
    }

    (claim_point, claims) = prove_batch_internal_round(
        prover_state,
        &witness.batch_partial_round_input,
        &witness.committed_cubes,
        &layers.batch_partial_rounds,
        &claim_point,
        &claims,
        &selectors,
    );

    let pcs_point_for_cubes = claim_point.clone();

    claims = claims[..WIDTH].to_vec();

    for (input_layers, full_round) in witness
        .remaining_initial_full_round_inputs
        .iter()
        .zip(&layers.initial_full_rounds_remaining)
        .rev()
    {
        (claim_point, claims) = prove_gkr_round(
            prover_state,
            full_round,
            input_layers,
            &claim_point,
            &claims,
            univariate_skips,
        );
    }
    (claim_point, _) = prove_gkr_round(
        prover_state,
        &layers.initial_full_round,
        &witness.input_layer,
        &claim_point,
        &claims,
        univariate_skips,
    );
    let pcs_point_for_inputs = claim_point.clone();

    let input_pcs_statements = inner_evals_on_commited_columns(
        prover_state,
        &pcs_point_for_inputs,
        univariate_skips,
        &witness.input_layer,
    );
    let cubes_pcs_statements = inner_evals_on_commited_columns(
        prover_state,
        &pcs_point_for_cubes,
        univariate_skips,
        &witness.committed_cubes,
    );

    (
        output_claims.try_into().unwrap(),
        input_pcs_statements,
        cubes_pcs_statements,
    )
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
    input_layers: &[impl AsRef<[PFPacking<EF>]>],
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
        MleGroupRef::BasePacked(input_layers.iter().map(|l| l.as_ref()).collect()),
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

fn inner_evals_on_commited_columns(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    point: &[EF],
    univariate_skips: usize,
    columns: &[Vec<PFPacking<EF>>],
) -> (MultilinearPoint<EF>, Vec<EF>) {
    let eq_mle = eval_eq_packed(&point[1..]);
    let inner_evals = columns
        .par_iter()
        .map(|col| {
            col.chunks_exact(eq_mle.len())
                .map(|chunk| {
                    let ef_sum = dot_product::<EFPacking<EF>, _, _>(
                        eq_mle.iter().copied(),
                        chunk.iter().copied(),
                    );
                    <EFPacking<EF> as PackedFieldExtension<F, EF>>::to_ext_iter([ef_sum])
                        .sum::<EF>()
                })
                .collect::<Vec<_>>()
        })
        .flatten()
        .collect::<Vec<_>>();
    prover_state.add_extension_scalars(&inner_evals);
    let mut values_to_prove = vec![];
    let pcs_batching_scalars_inputs = prover_state.sample_vec(univariate_skips);
    let point_to_prove =
        MultilinearPoint([pcs_batching_scalars_inputs.clone(), point[1..].to_vec()].concat());
    for col_inner_evals in inner_evals.chunks_exact(1 << univariate_skips) {
        values_to_prove
            .push(col_inner_evals.evaluate(&MultilinearPoint(pcs_batching_scalars_inputs.clone())));
    }
    (point_to_prove, values_to_prove)
}
