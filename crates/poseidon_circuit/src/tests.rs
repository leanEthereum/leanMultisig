#![cfg_attr(not(test), allow(unused_crate_dependencies))]

use multilinear_toolkit::prelude::*;
use p3_koala_bear::{KoalaBear, QuinticExtensionFieldKB};
use rand::{Rng, SeedableRng, rngs::StdRng};
use std::{array, time::Instant};
use utils::{
    build_prover_state, build_verifier_state, init_tracing, poseidon16_permute_mut,
    transposed_par_iter_mut,
};
use whir_p3::{
    FoldingFactor, SecurityAssumption, WhirConfig, WhirConfigBuilder, precompute_dft_twiddles,
};

use crate::{
    generate_poseidon_witness, gkr_layers::PoseidonGKRLayers, prove_poseidon_gkr,
    verify_poseidon_gkr,
};

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

        let claim_point = prover_state.sample_vec(log_n_poseidons + 1 - UNIVARIATE_SKIPS);

        let (pcs_point_for_inputs, pcs_point_for_cubes) = prove_poseidon_gkr(
            &mut prover_state,
            &witness,
            claim_point,
            UNIVARIATE_SKIPS,
            &layers,
        );

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

        let (
            (pcs_point_for_inputs, pcs_evals_for_inputs),
            (pcs_point_for_cubes, pcs_evals_for_cubes),
        ) = verify_poseidon_gkr(
            &mut verifier_state,
            log_n_poseidons,
            &output_claim_point,
            &layers,
            UNIVARIATE_SKIPS,
        );

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
