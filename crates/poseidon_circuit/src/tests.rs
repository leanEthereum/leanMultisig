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
    poseidon24_permute_mut, transposed_par_iter_mut,
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

const WIDTH: usize = 16;

const UNIVARIATE_SKIPS: usize = 3;
const N_COMMITED_CUBES: usize = 16;
const COMPRESS: bool = false;
const COMPRESSION_OUTPUT_WIDTH: usize = 8;

#[test]
fn test_prove_poseidons() {
    init_tracing();
    precompute_dft_twiddles::<F>(1 << 24);

    let log_n_poseidons = 20;

    let whir_config_builder = WhirConfigBuilder {
        folding_factor: FoldingFactor::new(7, 4),
        soundness_type: SecurityAssumption::CapacityBound,
        pow_bits: 16,
        max_num_variables_to_send_coeffs: 6,
        rs_domain_initial_reduction_factor: 5,
        security_level: 128,
        starting_log_inv_rate: 1,
    };
    let whir_n_vars = log_n_poseidons + log2_ceil_usize(WIDTH + N_COMMITED_CUBES);
    let whir_config = WhirConfig::new(whir_config_builder.clone(), whir_n_vars);

    let mut rng = StdRng::seed_from_u64(0);
    let n_poseidons = 1 << log_n_poseidons;
    let n_compressions = if COMPRESS { n_poseidons / 3 } else { 0 };

    let perm_inputs = (0..n_poseidons)
        .map(|_| rng.random())
        .collect::<Vec<[F; WIDTH]>>();
    let input: [_; WIDTH] =
        array::from_fn(|i| perm_inputs.par_iter().map(|x| x[i]).collect::<Vec<F>>());
    let input_packed: [_; WIDTH] =
        array::from_fn(|i| PFPacking::<EF>::pack_slice(&input[i]).to_vec());

    let layers = PoseidonGKRLayers::<WIDTH, N_COMMITED_CUBES>::build(
        COMPRESS.then(|| COMPRESSION_OUTPUT_WIDTH),
    );

    let default_cubes = default_cube_layers::<F, WIDTH, N_COMMITED_CUBES>(&layers);
    let input_col_dims = vec![ColDims::padded(n_poseidons, F::ZERO); WIDTH];
    let cubes_col_dims = default_cubes
        .iter()
        .map(|&v| ColDims::padded(n_poseidons, v))
        .collect::<Vec<_>>();
    let committed_col_dims = [input_col_dims, cubes_col_dims].concat();

    let log_smallest_decomposition_chunk = 0; // unused because everything is a power of 2

    let (mut verifier_state, proof_size, output_layer, prover_duration) = {
        // ---------------------------------------------------- PROVER ----------------------------------------------------

        let prover_time = Instant::now();

        let witness = generate_poseidon_witness::<FPacking<F>, WIDTH, N_COMMITED_CUBES>(
            input_packed,
            &layers,
            if COMPRESS {
                Some((
                    n_compressions,
                    PFPacking::<F>::pack_slice(
                        &[
                            vec![F::ZERO; n_poseidons - n_compressions],
                            vec![F::ONE; n_compressions],
                        ]
                        .concat(),
                    )
                    .to_vec(),
                ))
            } else {
                None
            },
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

        let (_output_values, input_pcs_statements, cubes_pcs_statements) = prove_poseidon_gkr(
            &mut prover_state,
            &witness,
            claim_point,
            UNIVARIATE_SKIPS,
            &layers,
        );

        // PCS opening
        let mut pcs_statements = vec![];
        for (point_to_prove, evals_to_prove) in [input_pcs_statements, cubes_pcs_statements] {
            for v in evals_to_prove {
                pcs_statements.push(vec![Evaluation {
                    point: point_to_prove.clone(),
                    value: v,
                }]);
            }
        }

        let global_statements = packed_pcs_global_statements_for_prover(
            &committed_polys,
            &committed_col_dims,
            log_smallest_decomposition_chunk,
            &pcs_statements,
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

        let (_output_values, input_pcs_statements, cubes_pcs_statements) = verify_poseidon_gkr(
            &mut verifier_state,
            log_n_poseidons,
            &output_claim_point,
            &layers,
            UNIVARIATE_SKIPS,
            if COMPRESS {
                Some(n_compressions)
            } else {
                None
            },
        );

        // PCS verification
        let mut pcs_statements = vec![];
        for (point_to_verif, evals_to_verif) in [input_pcs_statements, cubes_pcs_statements] {
            for v in evals_to_verif {
                pcs_statements.push(vec![Evaluation {
                    point: point_to_verif.clone(),
                    value: v,
                }]);
            }
        }

        let global_statements = packed_pcs_global_statements_for_verifier(
            &committed_col_dims,
            log_smallest_decomposition_chunk,
            &pcs_statements,
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

    let mut data_to_hash = input.clone();
    let plaintext_time = Instant::now();
    transposed_par_iter_mut(&mut data_to_hash).for_each(|row| {
        if WIDTH == 16 {
            let mut buff = array::from_fn(|j| *row[j]);
            poseidon16_permute_mut(&mut buff);
            for j in 0..WIDTH {
                *row[j] = buff[j];
            }
        } else if WIDTH == 24 {
            let mut buff = array::from_fn(|j| *row[j]);
            poseidon24_permute_mut(&mut buff);
            for j in 0..WIDTH {
                *row[j] = buff[j];
            }
        } else {
            panic!("Unsupported WIDTH");
        }
    });
    let plaintext_duration = plaintext_time.elapsed();

    // sanity check: ensure the plaintext poseidons matches the last GKR layer:
    if COMPRESS {
        output_layer
            .iter()
            .enumerate()
            .take(COMPRESSION_OUTPUT_WIDTH)
            .for_each(|(i, layer)| {
                assert_eq!(PFPacking::<EF>::unpack_slice(&layer), data_to_hash[i]);
            });
        output_layer
            .iter()
            .enumerate()
            .skip(COMPRESSION_OUTPUT_WIDTH)
            .for_each(|(i, layer)| {
                assert_eq!(
                    &PFPacking::<EF>::unpack_slice(&layer)[..n_poseidons - n_compressions],
                    &data_to_hash[i][..n_poseidons - n_compressions]
                );
                assert!(
                    PFPacking::<EF>::unpack_slice(&layer)[n_poseidons - n_compressions..]
                        .iter()
                        .all(|&x| x.is_zero())
                );
            });
    } else {
        output_layer.iter().enumerate().for_each(|(i, layer)| {
            assert_eq!(PFPacking::<EF>::unpack_slice(&layer), data_to_hash[i]);
        });
    }

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
