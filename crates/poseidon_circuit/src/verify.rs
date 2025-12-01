use multilinear_toolkit::prelude::*;
use p3_koala_bear::{KoalaBearInternalLayerParameters, KoalaBearParameters};
use p3_monty_31::InternalLayerBaseParameters;

use crate::{
    CompressionComputation, EF, F, FullRoundComputation, GKRPoseidonResult, PartialRoundComputation,
    build_poseidon_inv_matrices, gkr_layers::PoseidonGKRLayers,
};

pub fn verify_poseidon_gkr<const WIDTH: usize, const N_COMMITED_CUBES: usize>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    log_n_poseidons: usize,
    output_claim_point: &[EF],
    layers: &PoseidonGKRLayers<WIDTH, N_COMMITED_CUBES>,
    univariate_skips: usize,
    compression: bool,
) -> GKRPoseidonResult
where
    KoalaBearInternalLayerParameters: InternalLayerBaseParameters<KoalaBearParameters, WIDTH>,
{
    let selectors = univariate_selectors::<F>(univariate_skips);
    let (inv_mds_matrix, inv_light_matrix) = build_poseidon_inv_matrices::<WIDTH>();

    let mut output_claims = vec![];
    let mut claims = vec![];

    let mut point = {
        let inner_evals = (0..WIDTH)
            .map(|_| {
                verifier_state
                    .next_extension_scalars_vec(1 << univariate_skips)
                    .unwrap()
            })
            .collect::<Vec<_>>();
        let alpha = verifier_state.sample();
        let selectors_at_alpha = selectors
            .iter()
            .map(|selector| selector.evaluate(alpha))
            .collect::<Vec<_>>();
        for evals in inner_evals {
            output_claims.push(evals.evaluate(&MultilinearPoint(output_claim_point[..univariate_skips].to_vec())));
            claims.push(dot_product(selectors_at_alpha.iter().copied(), evals.into_iter()))
        }
        [vec![alpha], output_claim_point[univariate_skips..].to_vec()].concat()
    };

    let on_compression_selector = if compression {
        (point, claims) = verify_gkr_round(
            verifier_state,
            &CompressionComputation::<WIDTH> {
                compressed_output: layers.compressed_output.unwrap(),
            },
            log_n_poseidons,
            &point,
            &claims,
            univariate_skips,
            WIDTH + 1,
        );

        let inner_evals = verifier_state
            .next_extension_scalars_vec(1 << univariate_skips)
            .unwrap();
        let recomputed_value =
            evaluate_univariate_multilinear::<_, _, _, false>(&inner_evals, &[point[0]], &selectors, None);
        assert_eq!(claims.pop().unwrap(), recomputed_value);
        let epsilons = verifier_state.sample_vec(univariate_skips);
        let new_point = MultilinearPoint([epsilons.clone(), point[1..].to_vec()].concat());
        let new_eval = inner_evals.evaluate(&MultilinearPoint(epsilons));

        Some(Evaluation::new(new_point, new_eval))
    } else {
        None
    };

    for full_round_constants in layers.final_full_rounds.iter().rev() {
        claims = apply_matrix(&inv_mds_matrix, &claims);

        (point, claims) = verify_gkr_round(
            verifier_state,
            &FullRoundComputation {},
            log_n_poseidons,
            &point,
            &claims,
            univariate_skips,
            WIDTH,
        );

        for (claim, c) in claims.iter_mut().zip(full_round_constants) {
            *claim -= *c;
        }
    }

    for partial_round_constant in layers.partial_rounds_remaining.iter().rev() {
        claims = apply_matrix(&inv_light_matrix, &claims);

        (point, claims) = verify_gkr_round(
            verifier_state,
            &PartialRoundComputation::<WIDTH> {},
            log_n_poseidons,
            &point,
            &claims,
            univariate_skips,
            WIDTH,
        );

        claims[0] -= *partial_round_constant;
    }

    let mut pcs_point_for_cubes = vec![];
    let mut pcs_evals_for_cubes = vec![];
    if N_COMMITED_CUBES > 0 {
        let claimed_cubes_evals = verifier_state.next_extension_scalars_vec(N_COMMITED_CUBES).unwrap();

        (point, claims) = verify_gkr_round(
            verifier_state,
            layers.batch_partial_rounds.as_ref().unwrap(),
            log_n_poseidons,
            &point,
            &[claims, claimed_cubes_evals.clone()].concat(),
            univariate_skips,
            WIDTH + N_COMMITED_CUBES,
        );

        pcs_point_for_cubes = point.clone();
        pcs_evals_for_cubes = claims[WIDTH..].to_vec();

        claims = claims[..WIDTH].to_vec();
    }

    for full_round_constants in layers.initial_full_rounds.iter().rev() {
        claims = apply_matrix(&inv_mds_matrix, &claims);

        (point, claims) = verify_gkr_round(
            verifier_state,
            &FullRoundComputation {},
            log_n_poseidons,
            &point,
            &claims,
            univariate_skips,
            WIDTH,
        );

        for (claim, c) in claims.iter_mut().zip(full_round_constants) {
            *claim -= *c;
        }
    }

    claims = apply_matrix(&inv_mds_matrix, &claims);

    let pcs_point_for_inputs = point.clone();
    let pcs_evals_for_inputs = claims;

    let input_statements = verify_inner_evals_on_commited_columns(
        verifier_state,
        &pcs_point_for_inputs,
        &pcs_evals_for_inputs,
        &selectors,
    );

    let cubes_statements = if N_COMMITED_CUBES == 0 {
        Default::default()
    } else {
        verify_inner_evals_on_commited_columns(verifier_state, &pcs_point_for_cubes, &pcs_evals_for_cubes, &selectors)
    };

    let output_statements = MultiEvaluation::new(MultilinearPoint(output_claim_point.to_vec()), output_claims);
    GKRPoseidonResult {
        output_statements,
        input_statements,
        cubes_statements,
        on_compression_selector,
    }
}

fn verify_gkr_round<SC: SumcheckComputation<EF, ExtraData = ()>>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    computation: &SC,
    log_n_poseidons: usize,
    claim_point: &[EF],
    output_claims: &[EF],
    univariate_skips: usize,
    n_inputs: usize,
) -> (Vec<EF>, Vec<EF>) {
    let batching_scalar = verifier_state.sample();
    let batching_scalars_powers = batching_scalar.powers().collect_n(output_claims.len());
    let batched_claim: EF = dot_product(output_claims.iter().copied(), batching_scalar.powers());

    let (retrieved_batched_claim, sumcheck_postponed_claim) = sumcheck_verify_with_univariate_skip(
        verifier_state,
        computation.max_degree() + 1,
        log_n_poseidons,
        univariate_skips,
    )
    .unwrap();

    assert_eq!(retrieved_batched_claim, batched_claim);

    let sumcheck_inner_evals = verifier_state.next_extension_scalars_vec(n_inputs).unwrap();
    assert_eq!(
        computation.eval_extension(&sumcheck_inner_evals, &[], &(), &batching_scalars_powers, 0)
            * eq_poly_with_skip(&sumcheck_postponed_claim.point, claim_point, univariate_skips),
        sumcheck_postponed_claim.value
    );

    (sumcheck_postponed_claim.point.0, sumcheck_inner_evals)
}

fn verify_inner_evals_on_commited_columns(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    point: &[EF],
    claimed_evals: &[EF],
    selectors: &[DensePolynomial<F>],
) -> MultiEvaluation<EF> {
    let univariate_skips = log2_strict_usize(selectors.len());
    let inner_evals_inputs = verifier_state
        .next_extension_scalars_vec(claimed_evals.len() << univariate_skips)
        .unwrap();
    let pcs_batching_scalars_inputs = verifier_state.sample_vec(univariate_skips);
    let mut values_to_verif = vec![];
    let point_to_verif = MultilinearPoint([pcs_batching_scalars_inputs.clone(), point[1..].to_vec()].concat());
    for (&eval, col_inner_evals) in claimed_evals
        .iter()
        .zip(inner_evals_inputs.chunks_exact(1 << univariate_skips))
    {
        assert_eq!(
            eval,
            evaluate_univariate_multilinear::<_, _, _, false>(col_inner_evals, &point[..1], selectors, None)
        );
        values_to_verif.push(col_inner_evals.evaluate(&MultilinearPoint(pcs_batching_scalars_inputs.clone())));
    }
    MultiEvaluation::new(point_to_verif, values_to_verif)
}
