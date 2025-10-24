#![cfg_attr(not(test), allow(unused_crate_dependencies))]

use multilinear_toolkit::prelude::*;
use p3_koala_bear::{KoalaBear, QuinticExtensionFieldKB};
use rand::{Rng, SeedableRng, rngs::StdRng};
use std::{array, time::Instant};
use tracing::{info_span, instrument};
use utils::{
    build_prover_state, build_verifier_state, init_tracing, poseidon16_permute_mut,
    transposed_par_iter_mut,
};
use whir_p3::{
    FoldingFactor, SecurityAssumption, WhirConfig, WhirConfigBuilder, precompute_dft_twiddles,
};

use crate::{generate_poseidon_witness, gkr_layers::{BatchPartialRounds, PoseidonGKRLayers}};

type F = KoalaBear;
type EF = QuinticExtensionFieldKB;
const UNIVARIATE_SKIPS: usize = 3;

const WIDTH: usize = 16;
const N_COMMITED_CUBES: usize = 16; // power of 2 to increase PCS efficiency

#[test]
fn test_prove_poseidons() {
    init_tracing();
    precompute_dft_twiddles::<F>(1 << 24);

    let log_n_poseidons = 20;

    let whir_config_builder = WhirConfigBuilder {
        folding_factor: FoldingFactor::new(7, 4),
        soundness_type: SecurityAssumption::CapacityBound,
        pow_bits: WIDTH,
        max_num_variables_to_send_coeffs: 6,
        rs_domain_initial_reduction_factor: 5,
        security_level: 128,
        starting_log_inv_rate: 1,
    };
    let whir_n_vars = log_n_poseidons + log2_strict_usize(WIDTH + N_COMMITED_CUBES);
    let whir_config = WhirConfig::new(whir_config_builder, whir_n_vars);

    let mut rng = StdRng::seed_from_u64(0);
    let n_poseidons = 1 << log_n_poseidons;
    let perm_inputs = (0..n_poseidons)
        .map(|_| rng.random())
        .collect::<Vec<[F; WIDTH]>>();
    let selectors = univariate_selectors::<F>(UNIVARIATE_SKIPS);
    let input_layers: [_; WIDTH] =
        array::from_fn(|i| perm_inputs.par_iter().map(|x| x[i]).collect::<Vec<F>>());
    let input_layers_packed: [_; WIDTH] =
        array::from_fn(|i| PFPacking::<EF>::pack_slice(&input_layers[i]).to_vec());

    let layers = PoseidonGKRLayers::<WIDTH, N_COMMITED_CUBES>::build();

    let (mut verifier_state, proof_size, output_layer, prover_duration) = {
        // ---------------------------------------------------- PROVER ----------------------------------------------------

        let prover_time = Instant::now();

        let witness =
            generate_poseidon_witness::<WIDTH, N_COMMITED_CUBES>(input_layers_packed, &layers);

        let mut prover_state = build_prover_state::<EF>();
        let mut global_poly_commited: Vec<F> = unsafe { uninitialized_vec(1 << whir_n_vars) };
        let mut chunks = split_at_mut_many(
            &mut global_poly_commited,
            (0..WIDTH + N_COMMITED_CUBES - 1)
                .map(|i| (i + 1) << log_n_poseidons)
                .collect::<Vec<_>>()
                .as_slice(),
        );
        chunks[..WIDTH]
            .par_iter_mut()
            .enumerate()
            .for_each(|(i, chunk)| {
                chunk.copy_from_slice(&input_layers[i]);
            });
        chunks[WIDTH..]
            .par_iter_mut()
            .enumerate()
            .for_each(|(i, chunk)| {
                chunk.copy_from_slice(PFPacking::<EF>::unpack_slice(&witness.committed_cubes[i]));
            });

        let global_poly_commited = MleOwned::Base(global_poly_commited);
        let pcs_witness = whir_config.commit(&mut prover_state, &global_poly_commited);
        let global_poly_commited_packed =
            PFPacking::<EF>::pack_slice(global_poly_commited.as_base().unwrap());

        let mut claim_point = prover_state.sample_vec(log_n_poseidons + 1 - UNIVARIATE_SKIPS);

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
                &mut prover_state,
                full_round,
                input_layers,
                &claim_point,
                &output_claims,
            );
        }

        for (input_layers, partial_round) in witness
            .remaining_partial_round_inputs
            .iter()
            .zip(&layers.partial_rounds_remaining)
            .rev()
        {
            (claim_point, output_claims) = prove_gkr_round(
                &mut prover_state,
                partial_round,
                input_layers,
                &claim_point,
                &output_claims,
            );
        }

        (claim_point, output_claims) = prove_batch_internal_rounds(
            &mut prover_state,
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
                &mut prover_state,
                full_round,
                input_layers,
                &claim_point,
                &output_claims,
            );
        }
        (claim_point, _) = prove_gkr_round(
            &mut prover_state,
            &layers.initial_full_round,
            &witness.input_layer,
            &claim_point,
            &output_claims,
        );

        let pcs_point_for_inputs = claim_point.clone();

        // PCS opening
        let mut pcs_statements = vec![];

        let eq_mle_inputs = eval_eq_packed(&pcs_point_for_inputs[1..]);
        let inner_evals_inputs = global_poly_commited_packed
            [..global_poly_commited_packed.len() / 2]
            .par_chunks_exact(eq_mle_inputs.len())
            .map(|chunk| {
                let ef_sum = dot_product::<EFPacking<EF>, _, _>(
                    eq_mle_inputs.iter().copied(),
                    chunk.iter().copied(),
                );
                <EFPacking<EF> as PackedFieldExtension<F, EF>>::to_ext_iter([ef_sum]).sum::<EF>()
            })
            .collect::<Vec<_>>();
        prover_state.add_extension_scalars(&inner_evals_inputs);
        let pcs_batching_scalars_inputs = prover_state.sample_vec(4 + UNIVARIATE_SKIPS); // 4 = log2(WIDTH)
        pcs_statements.push(Evaluation {
            point: MultilinearPoint(
                [
                    vec![EF::ZERO],
                    pcs_batching_scalars_inputs.clone(),
                    pcs_point_for_inputs[1..].to_vec(),
                ]
                .concat(),
            ),
            value: inner_evals_inputs.evaluate(&MultilinearPoint(pcs_batching_scalars_inputs)),
        });

        let eq_mle_cubes = eval_eq_packed(&pcs_point_for_cubes[1..]);
        let inner_evals_cubes = global_poly_commited_packed
            [global_poly_commited_packed.len() / 2..]
            .par_chunks_exact(eq_mle_cubes.len())
            .map(|chunk| {
                let ef_sum = dot_product::<EFPacking<EF>, _, _>(
                    eq_mle_cubes.iter().copied(),
                    chunk.iter().copied(),
                );
                <EFPacking<EF> as PackedFieldExtension<F, EF>>::to_ext_iter([ef_sum]).sum::<EF>()
            })
            .collect::<Vec<_>>();
        prover_state.add_extension_scalars(&inner_evals_cubes);
        let pcs_batching_scalars_cubes =
            prover_state.sample_vec(log2_strict_usize(N_COMMITED_CUBES) + UNIVARIATE_SKIPS);
        pcs_statements.push(Evaluation {
            point: MultilinearPoint(
                [
                    vec![EF::ONE],
                    pcs_batching_scalars_cubes.clone(),
                    pcs_point_for_cubes[1..].to_vec(),
                ]
                .concat(),
            ),
            value: inner_evals_cubes.evaluate(&MultilinearPoint(pcs_batching_scalars_cubes)),
        });

        whir_config.prove(
            &mut prover_state,
            pcs_statements,
            pcs_witness,
            &global_poly_commited.by_ref(),
        );

        let prover_duration = prover_time.elapsed();

        (
            build_verifier_state(&prover_state),
            prover_state.proof_size(),
            witness.output_layer,
            prover_duration,
        )
    };

    let verifier_time = Instant::now();
    {
        // ---------------------------------------------------- VERIFIER ----------------------------------------------------

        let parsed_pcs_commitment = whir_config
            .parse_commitment::<F>(&mut verifier_state)
            .unwrap();

        let output_claim_point = verifier_state.sample_vec(log_n_poseidons + 1 - UNIVARIATE_SKIPS);

        let mut output_claims = verifier_state.next_extension_scalars_vec(WIDTH).unwrap();

        let mut claim_point = output_claim_point.clone();
        for full_round in layers.final_full_rounds.iter().rev() {
            (claim_point, output_claims) = verify_gkr_round(
                &mut verifier_state,
                full_round,
                log_n_poseidons,
                &claim_point,
                &output_claims,
            );
        }

        for partial_round in layers.partial_rounds_remaining.iter().rev() {
            (claim_point, output_claims) = verify_gkr_round(
                &mut verifier_state,
                partial_round,
                log_n_poseidons,
                &claim_point,
                &output_claims,
            );
        }
        let claimed_cubes_evals = verifier_state
            .next_extension_scalars_vec(N_COMMITED_CUBES)
            .unwrap();

        (claim_point, output_claims) = verify_gkr_round(
            &mut verifier_state,
            &layers.batch_partial_rounds,
            log_n_poseidons,
            &claim_point,
            &[output_claims, claimed_cubes_evals.clone()].concat(),
        );

        let pcs_point_for_cubes = claim_point.clone();
        let pcs_evals_for_cubes = output_claims[WIDTH..].to_vec();

        output_claims = output_claims[..WIDTH].to_vec();

        for full_round in layers.initial_full_rounds_remaining.iter().rev() {
            (claim_point, output_claims) = verify_gkr_round(
                &mut verifier_state,
                full_round,
                log_n_poseidons,
                &claim_point,
                &output_claims,
            );
        }
        (claim_point, output_claims) = verify_gkr_round(
            &mut verifier_state,
            &layers.initial_full_round,
            log_n_poseidons,
            &claim_point,
            &output_claims,
        );

        let pcs_point_for_inputs = claim_point.clone();
        let pcs_evals_for_inputs = output_claims.to_vec();

        // PCS verification

        let mut pcs_statements = vec![];

        let inner_evals_inputs = verifier_state
            .next_extension_scalars_vec(WIDTH << UNIVARIATE_SKIPS)
            .unwrap();
        let pcs_batching_scalars_inputs = verifier_state.sample_vec(4 + UNIVARIATE_SKIPS); // 4 = log2(WIDTH)
        pcs_statements.push(Evaluation {
            point: MultilinearPoint(
                [
                    vec![EF::ZERO],
                    pcs_batching_scalars_inputs.clone(),
                    pcs_point_for_inputs[1..].to_vec(),
                ]
                .concat(),
            ),
            value: inner_evals_inputs.evaluate(&MultilinearPoint(pcs_batching_scalars_inputs)),
        });
        {
            for (&eval, inner_evals) in pcs_evals_for_inputs
                .iter()
                .zip(inner_evals_inputs.chunks_exact(1 << UNIVARIATE_SKIPS))
            {
                assert_eq!(
                    eval,
                    evaluate_univariate_multilinear::<_, _, _, false>(
                        inner_evals,
                        &pcs_point_for_inputs[..1],
                        &selectors,
                        None
                    )
                );
            }
        }

        let inner_evals_cubes = verifier_state
            .next_extension_scalars_vec(N_COMMITED_CUBES << UNIVARIATE_SKIPS)
            .unwrap();
        let pcs_batching_scalars_cubes =
            verifier_state.sample_vec(log2_strict_usize(N_COMMITED_CUBES) + UNIVARIATE_SKIPS);
        pcs_statements.push(Evaluation {
            point: MultilinearPoint(
                [
                    vec![EF::ONE],
                    pcs_batching_scalars_cubes.clone(),
                    pcs_point_for_cubes[1..].to_vec(),
                ]
                .concat(),
            ),
            value: inner_evals_cubes.evaluate(&MultilinearPoint(pcs_batching_scalars_cubes)),
        });
        {
            for (&eval, inner_evals) in pcs_evals_for_cubes
                .iter()
                .zip(inner_evals_cubes.chunks_exact(1 << UNIVARIATE_SKIPS))
            {
                assert_eq!(
                    eval,
                    evaluate_univariate_multilinear::<_, _, _, false>(
                        inner_evals,
                        &pcs_point_for_cubes[..1],
                        &selectors,
                        None
                    )
                );
            }
        }

        whir_config
            .verify(&mut verifier_state, &parsed_pcs_commitment, pcs_statements)
            .unwrap();
    }
    let verifier_duration = verifier_time.elapsed();

    let mut data_to_hash = input_layers.clone();
    let plaintext_time = Instant::now();
    transposed_par_iter_mut(&mut data_to_hash).for_each(|row| {
        let mut buff = array::from_fn(|j| *row[j]);
        poseidon16_permute_mut(&mut buff);
        for j in 0..WIDTH {
            *row[j] = buff[j];
        }
    });
    let plaintext_duration = plaintext_time.elapsed();

    // sanity check: ensure the plaintext poseidons matches the last GKR layer:
    output_layer.iter().enumerate().for_each(|(i, layer)| {
        assert_eq!(PFPacking::<EF>::unpack_slice(&layer), data_to_hash[i]);
    });

    println!("2^{} Poseidon2", log_n_poseidons);
    println!(
        "Plaintext (no proof) time: {:.3}s ({:.2}M Poseidons / s)",
        plaintext_duration.as_secs_f64(),
        n_poseidons as f64 / (plaintext_duration.as_secs_f64() * 1e6)
    );
    println!(
        "Prover time: {:.3}s ({:.2}M Poseidons / s, {:.1}x slower than plaintext)",
        prover_duration.as_secs_f64(),
        n_poseidons as f64 / (prover_duration.as_secs_f64() * 1e6),
        prover_duration.as_secs_f64() / plaintext_duration.as_secs_f64()
    );
    println!(
        "Proof size: {:.1} KiB (without merkle pruning)",
        (proof_size * F::bits()) as f64 / (8.0 * 1024.0)
    );
    println!("Verifier time: {}ms", verifier_duration.as_millis());
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
) -> (Vec<EF>, Vec<EF>) {
    let batching_scalar = prover_state.sample();
    let batched_claim: EF = dot_product(output_claims.iter().copied(), batching_scalar.powers());
    let batching_scalars_powers = batching_scalar.powers().collect_n(WIDTH);

    let (sumcheck_point, sumcheck_inner_evals, sumcheck_final_sum) = sumcheck_prove(
        UNIVARIATE_SKIPS,
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
            * eq_poly_with_skip(&sumcheck_point, &claim_point, UNIVARIATE_SKIPS),
        sumcheck_final_sum
    );

    prover_state.add_extension_scalars(&sumcheck_inner_evals);

    (sumcheck_point.0, sumcheck_inner_evals)
}

#[instrument(skip_all)]
fn prove_batch_internal_rounds(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    input_layers: &[Vec<PFPacking<EF>>],
    committed_cubes: &[Vec<PFPacking<EF>>],
    computation: &BatchPartialRounds<WIDTH, N_COMMITED_CUBES>,
    claim_point: &[EF],
    output_claims: &[EF],
    selectors: &[DensePolynomial<F>],
) -> (Vec<EF>, Vec<EF>) {
    assert_eq!(input_layers.len(), WIDTH);
    assert_eq!(committed_cubes.len(), N_COMMITED_CUBES);

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
        UNIVARIATE_SKIPS,
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
            * eq_poly_with_skip(&sumcheck_point, &claim_point, UNIVARIATE_SKIPS),
        sumcheck_final_sum
    );

    prover_state.add_extension_scalars(&sumcheck_inner_evals);

    (sumcheck_point.0, sumcheck_inner_evals)
}

fn verify_gkr_round<SC: SumcheckComputation<EF, EF>>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    computation: &SC,
    log_n_poseidons: usize,
    claim_point: &[EF],
    output_claims: &[EF],
) -> (Vec<EF>, Vec<EF>) {
    let batching_scalar = verifier_state.sample();
    let batching_scalars_powers = batching_scalar.powers().collect_n(output_claims.len());
    let batched_claim: EF = dot_product(output_claims.iter().copied(), batching_scalar.powers());

    let (retrieved_batched_claim, sumcheck_postponed_claim) = sumcheck_verify_with_univariate_skip(
        verifier_state,
        computation.degree() + 1,
        log_n_poseidons,
        UNIVARIATE_SKIPS,
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
                UNIVARIATE_SKIPS
            ),
        sumcheck_postponed_claim.value
    );

    (sumcheck_postponed_claim.point.0, sumcheck_inner_evals)
}
