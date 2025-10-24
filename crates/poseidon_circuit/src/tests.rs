#![cfg_attr(not(test), allow(unused_crate_dependencies))]

use multilinear_toolkit::prelude::*;
use p3_koala_bear::{KoalaBear, QuinticExtensionFieldKB};
use packed_pcs::{
    ColDims, packed_pcs_commit, packed_pcs_global_statements_for_prover,
    packed_pcs_global_statements_for_verifier, packed_pcs_parse_commitment,
};
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
    default_cube_layers, generate_poseidon_witness, gkr_layers::PoseidonGKRLayers,
    prove_poseidon_gkr, verify_poseidon_gkr,
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
    let whir_config = WhirConfig::new(whir_config_builder.clone(), whir_n_vars);

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

    let default_cubes = default_cube_layers::<F, WIDTH, N_COMMITED_CUBES>(&layers);
    let input_col_dims = vec![ColDims::padded(n_poseidons, F::ZERO); WIDTH];
    let cubes_col_dims = default_cubes
        .iter()
        .map(|&v| ColDims::padded(n_poseidons, v))
        .collect::<Vec<_>>();
    let committed_col_dims = [input_col_dims, cubes_col_dims].concat();

    let log_smallest_decomposition_chunk = 10; // unused because everything is a power of 2

    let (mut verifier_state, proof_size, output_layer, prover_duration) = {
        // ---------------------------------------------------- PROVER ----------------------------------------------------

        let prover_time = Instant::now();

        let witness = generate_poseidon_witness::<FPacking<F>, WIDTH, N_COMMITED_CUBES>(
            input_layers_packed,
            &layers,
        );

        let mut prover_state = build_prover_state::<EF>();

        let committed_polys = witness
            .input_layer
            .iter()
            .chain(&witness.committed_cubes)
            .map(|s| PFPacking::<F>::unpack_slice(s))
            .collect::<Vec<_>>();

        let pcs_commitment_witness = packed_pcs_commit(
            &whir_config_builder,
            &committed_polys,
            &committed_col_dims,
            &mut prover_state,
            log_smallest_decomposition_chunk,
        );

        let claim_point = prover_state.sample_vec(log_n_poseidons + 1 - UNIVARIATE_SKIPS);

        let (pcs_point_for_inputs, pcs_point_for_cubes) = prove_poseidon_gkr(
            &mut prover_state,
            &witness,
            claim_point,
            UNIVARIATE_SKIPS,
            &layers,
        );

        // PCS opening

        let eq_mle_inputs = eval_eq_packed(&pcs_point_for_inputs[1..]);
        let inner_evals_inputs = witness
            .input_layer
            .par_iter()
            .map(|col| {
                col.chunks_exact(eq_mle_inputs.len())
                    .map(|chunk| {
                        let ef_sum = dot_product::<EFPacking<EF>, _, _>(
                            eq_mle_inputs.iter().copied(),
                            chunk.iter().copied(),
                        );
                        <EFPacking<EF> as PackedFieldExtension<F, EF>>::to_ext_iter([ef_sum])
                            .sum::<EF>()
                    })
                    .collect::<Vec<_>>()
            })
            .flatten()
            .collect::<Vec<_>>();
        assert_eq!(inner_evals_inputs.len(), WIDTH << UNIVARIATE_SKIPS);
        prover_state.add_extension_scalars(&inner_evals_inputs);
        let mut input_pcs_statements = vec![];
        let pcs_batching_scalars_inputs = prover_state.sample_vec(UNIVARIATE_SKIPS); // 4 = log2(WIDTH)
        for col_inner_evals in inner_evals_inputs.chunks_exact(1 << UNIVARIATE_SKIPS) {
            input_pcs_statements.push(vec![Evaluation {
                point: MultilinearPoint(
                    [
                        pcs_batching_scalars_inputs.clone(),
                        pcs_point_for_inputs[1..].to_vec(),
                    ]
                    .concat(),
                ),
                value: col_inner_evals
                    .evaluate(&MultilinearPoint(pcs_batching_scalars_inputs.clone())),
            }]);
        }

        let eq_mle_cubes = eval_eq_packed(&pcs_point_for_cubes[1..]);
        let inner_evals_cubes = witness
            .committed_cubes
            .par_iter()
            .map(|col| {
                col.chunks_exact(eq_mle_cubes.len())
                    .map(|chunk| {
                        let ef_sum = dot_product::<EFPacking<EF>, _, _>(
                            eq_mle_cubes.iter().copied(),
                            chunk.iter().copied(),
                        );
                        <EFPacking<EF> as PackedFieldExtension<F, EF>>::to_ext_iter([ef_sum])
                            .sum::<EF>()
                    })
                    .collect::<Vec<_>>()
            })
            .flatten()
            .collect::<Vec<_>>();
        assert_eq!(
            inner_evals_cubes.len(),
            N_COMMITED_CUBES << UNIVARIATE_SKIPS
        );
        prover_state.add_extension_scalars(&inner_evals_cubes);
        let mut cubes_pcs_statements = vec![];
        let pcs_batching_scalars_cubes = prover_state.sample_vec(UNIVARIATE_SKIPS);
        for col_inner_evals in inner_evals_cubes.chunks_exact(1 << UNIVARIATE_SKIPS) {
            cubes_pcs_statements.push(vec![Evaluation {
                point: MultilinearPoint(
                    [
                        pcs_batching_scalars_cubes.clone(),
                        pcs_point_for_cubes[1..].to_vec(),
                    ]
                    .concat(),
                ),
                value: col_inner_evals
                    .evaluate(&MultilinearPoint(pcs_batching_scalars_cubes.clone())),
            }]);
        }

        assert_eq!(committed_polys.len(), WIDTH + N_COMMITED_CUBES);
        assert_eq!(input_pcs_statements.len(), WIDTH);
        assert_eq!(cubes_pcs_statements.len(), N_COMMITED_CUBES);

        let global_statements = packed_pcs_global_statements_for_prover(
            &committed_polys,
            &committed_col_dims,
            log_smallest_decomposition_chunk,
            &[input_pcs_statements, cubes_pcs_statements].concat(),
            &mut prover_state,
        );
        whir_config.prove(
            &mut prover_state,
            global_statements,
            pcs_commitment_witness.inner_witness,
            &pcs_commitment_witness.packed_polynomial.by_ref(),
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

        let parsed_pcs_commitment = packed_pcs_parse_commitment(
            &whir_config_builder,
            &mut verifier_state,
            &committed_col_dims,
            log_smallest_decomposition_chunk,
        )
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

        let inner_evals_inputs = verifier_state
            .next_extension_scalars_vec(WIDTH << UNIVARIATE_SKIPS)
            .unwrap();
        let pcs_batching_scalars_inputs = verifier_state.sample_vec(UNIVARIATE_SKIPS);
        let mut input_pcs_statements = vec![];
        for (&eval, col_inner_evals) in pcs_evals_for_inputs
            .iter()
            .zip(inner_evals_inputs.chunks_exact(1 << UNIVARIATE_SKIPS))
        {
            assert_eq!(
                eval,
                evaluate_univariate_multilinear::<_, _, _, false>(
                    col_inner_evals,
                    &pcs_point_for_inputs[..1],
                    &selectors,
                    None
                )
            );
            input_pcs_statements.push(vec![Evaluation {
                point: MultilinearPoint(
                    [
                        pcs_batching_scalars_inputs.clone(),
                        pcs_point_for_inputs[1..].to_vec(),
                    ]
                    .concat(),
                ),
                value: col_inner_evals
                    .evaluate(&MultilinearPoint(pcs_batching_scalars_inputs.clone())),
            }]);
        }

        let inner_evals_cubes = verifier_state
            .next_extension_scalars_vec(N_COMMITED_CUBES << UNIVARIATE_SKIPS)
            .unwrap();
        let pcs_batching_scalars_cubes = verifier_state.sample_vec(UNIVARIATE_SKIPS);
        let mut cubes_pcs_statements = vec![];
        for (&eval, col_inner_evals) in pcs_evals_for_cubes
            .iter()
            .zip(inner_evals_cubes.chunks_exact(1 << UNIVARIATE_SKIPS))
        {
            assert_eq!(
                eval,
                evaluate_univariate_multilinear::<_, _, _, false>(
                    col_inner_evals,
                    &pcs_point_for_cubes[..1],
                    &selectors,
                    None
                )
            );
            cubes_pcs_statements.push(vec![Evaluation {
                point: MultilinearPoint(
                    [
                        pcs_batching_scalars_cubes.clone(),
                        pcs_point_for_cubes[1..].to_vec(),
                    ]
                    .concat(),
                ),
                value: col_inner_evals
                    .evaluate(&MultilinearPoint(pcs_batching_scalars_cubes.clone())),
            }]);
        }

        let global_statements = packed_pcs_global_statements_for_verifier(
            &committed_col_dims,
            log_smallest_decomposition_chunk,
            &[input_pcs_statements, cubes_pcs_statements].concat(),
            &mut verifier_state,
            &Default::default(),
        )
        .unwrap();

        whir_config
            .verify::<F>(
                &mut verifier_state,
                &parsed_pcs_commitment,
                global_statements,
            )
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
