use multilinear_toolkit::prelude::*;
use p3_koala_bear::{KoalaBear, KoalaBearInternalLayerParameters, KoalaBearParameters, QuinticExtensionFieldKB};
use p3_monty_31::InternalLayerBaseParameters;
use rand::{Rng, SeedableRng, rngs::StdRng};
use std::{array, time::Instant};
use sub_protocols::{
    ColDims, packed_pcs_commit, packed_pcs_global_statements_for_prover, packed_pcs_global_statements_for_verifier,
    packed_pcs_parse_commitment,
};
use utils::{
    build_prover_state, build_verifier_state, init_tracing, poseidon16_permute_mut, poseidon24_permute_mut,
    transposed_par_iter_mut,
};
use whir_p3::{FoldingFactor, SecurityAssumption, WhirConfig, WhirConfigBuilder, precompute_dft_twiddles};

use crate::{
    GKRPoseidonResult, default_cube_layers, generate_poseidon_witness, gkr_layers::PoseidonGKRLayers,
    prove_poseidon_gkr, verify_poseidon_gkr,
};

type F = KoalaBear;
type EF = QuinticExtensionFieldKB;

const COMPRESSION_OUTPUT_WIDTH: usize = 8;

#[test]
fn test_poseidon_benchmark() {
    run_poseidon_benchmark::<16, 0, 3>(12, false, false);
    run_poseidon_benchmark::<16, 0, 3>(12, true, false);
    run_poseidon_benchmark::<16, 16, 3>(12, false, false);
    run_poseidon_benchmark::<16, 16, 3>(12, true, false);
}

pub fn run_poseidon_benchmark<const WIDTH: usize, const N_COMMITED_CUBES: usize, const UNIVARIATE_SKIPS: usize>(
    log_n_poseidons: usize,
    compress: bool,
    tracing: bool,
) where
    KoalaBearInternalLayerParameters: InternalLayerBaseParameters<KoalaBearParameters, WIDTH>,
{
    if tracing {
        init_tracing();
    }
    precompute_dft_twiddles::<F>(1 << 24);

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
    let n_compressions = if compress { n_poseidons / 3 } else { 0 };

    let perm_inputs = (0..n_poseidons).map(|_| rng.random()).collect::<Vec<[F; WIDTH]>>();
    let input: [_; WIDTH] = array::from_fn(|i| perm_inputs.par_iter().map(|x| x[i]).collect::<Vec<F>>());
    let input_packed: [_; WIDTH] = array::from_fn(|i| PFPacking::<EF>::pack_slice(&input[i]).to_vec());

    let layers = PoseidonGKRLayers::<WIDTH, N_COMMITED_CUBES>::build(compress.then_some(COMPRESSION_OUTPUT_WIDTH));

    let default_cubes = default_cube_layers::<F, WIDTH, N_COMMITED_CUBES>(&layers);

    let input_col_dims = vec![ColDims::padded(n_poseidons, F::ZERO); WIDTH];
    let cubes_col_dims = default_cubes
        .iter()
        .map(|&v| ColDims::padded(n_poseidons, v))
        .collect::<Vec<_>>();
    let committed_col_dims = [input_col_dims, cubes_col_dims].concat();

    let log_smallest_decomposition_chunk = 0; // unused because everything is a power of 2

    let (mut verifier_state, proof_size_pcs, proof_size_gkr, output_layer, prover_duration, output_statements_prover) = {
        // ---------------------------------------------------- PROVER ----------------------------------------------------

        let prover_time = Instant::now();

        let witness = generate_poseidon_witness::<FPacking<F>, WIDTH, N_COMMITED_CUBES>(
            input_packed,
            &layers,
            if compress {
                Some(
                    PFPacking::<F>::pack_slice(
                        &[
                            vec![F::ZERO; n_poseidons - n_compressions],
                            vec![F::ONE; n_compressions],
                        ]
                        .concat(),
                    )
                    .to_vec(),
                )
            } else {
                None
            },
        );

        let mut prover_state = build_prover_state::<EF>(false);

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

        let claim_point = prover_state.sample_vec(log_n_poseidons);

        let GKRPoseidonResult {
            output_statements,
            input_statements,
            cubes_statements,
            on_compression_selector,
        } = prove_poseidon_gkr(
            &mut prover_state,
            &witness,
            claim_point.clone(),
            UNIVARIATE_SKIPS,
            &layers,
        );
        assert_eq!(&output_statements.point.0, &claim_point);
        if let Some(on_compression_selector) = on_compression_selector {
            assert_eq!(
                on_compression_selector.value,
                mle_of_zeros_then_ones((1 << log_n_poseidons) - n_compressions, &on_compression_selector.point,)
            );
        }

        // PCS opening
        let mut pcs_statements = vec![];
        for meval in [input_statements, cubes_statements] {
            for v in meval.values {
                pcs_statements.push(vec![Evaluation {
                    point: meval.point.clone(),
                    value: v,
                }]);
            }
        }

        let proof_size_gkr = prover_state.proof_size();

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

        let proof_size_pcs = prover_state.proof_size() - proof_size_gkr;
        (
            build_verifier_state(prover_state),
            proof_size_pcs,
            proof_size_gkr,
            match compress {
                false => witness.output_layer,
                true => witness.compression.unwrap().1,
            },
            prover_duration,
            output_statements,
        )
    };

    let verifier_time = Instant::now();

    let output_statements_verifier = {
        // ---------------------------------------------------- VERIFIER ----------------------------------------------------

        let parsed_pcs_commitment = packed_pcs_parse_commitment(
            &whir_config_builder,
            &mut verifier_state,
            &committed_col_dims,
            log_smallest_decomposition_chunk,
        )
        .unwrap();

        let output_claim_point = verifier_state.sample_vec(log_n_poseidons);

        let GKRPoseidonResult {
            output_statements,
            input_statements,
            cubes_statements,
            on_compression_selector,
        } = verify_poseidon_gkr(
            &mut verifier_state,
            log_n_poseidons,
            &output_claim_point,
            &layers,
            UNIVARIATE_SKIPS,
            compress,
        );
        assert_eq!(&output_statements.point.0, &output_claim_point);

        if let Some(on_compression_selector) = on_compression_selector {
            assert_eq!(
                on_compression_selector.value,
                mle_of_zeros_then_ones((1 << log_n_poseidons) - n_compressions, &on_compression_selector.point,)
            );
        }

        // PCS verification
        let mut pcs_statements = vec![];
        for meval in [input_statements, cubes_statements] {
            for v in meval.values {
                pcs_statements.push(vec![Evaluation {
                    point: meval.point.clone(),
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
            .verify::<F>(&mut verifier_state, &parsed_pcs_commitment, global_statements)
            .unwrap();
        output_statements
    };
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
    if compress {
        output_layer
            .iter()
            .enumerate()
            .take(COMPRESSION_OUTPUT_WIDTH)
            .for_each(|(i, layer)| {
                assert_eq!(PFPacking::<EF>::unpack_slice(layer), data_to_hash[i]);
            });
        output_layer
            .iter()
            .enumerate()
            .skip(COMPRESSION_OUTPUT_WIDTH)
            .for_each(|(i, layer)| {
                assert_eq!(
                    &PFPacking::<EF>::unpack_slice(layer)[..n_poseidons - n_compressions],
                    &data_to_hash[i][..n_poseidons - n_compressions]
                );
                assert!(
                    PFPacking::<EF>::unpack_slice(layer)[n_poseidons - n_compressions..]
                        .iter()
                        .all(|&x| x.is_zero())
                );
            });
    } else {
        output_layer.iter().enumerate().for_each(|(i, layer)| {
            assert_eq!(PFPacking::<EF>::unpack_slice(layer), data_to_hash[i]);
        });
    }
    assert_eq!(&output_statements_prover, &output_statements_verifier);
    assert_eq!(
        &output_statements_verifier.values,
        &output_layer
            .iter()
            .map(|layer| PFPacking::<EF>::unpack_slice(layer).evaluate(&output_statements_verifier.point))
            .collect::<Vec<_>>()
    );

    println!("2^{log_n_poseidons} Poseidon2");
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
        "Proof size: GKR = {:.1} KiB, PCS = {:.1} KiB . Total = {:.1} KiB (available optimizations: GKR = 40%, PCS = 15%)",
        (proof_size_gkr * F::bits()) as f64 / (8.0 * 1024.0),
        (proof_size_pcs * F::bits()) as f64 / (8.0 * 1024.0),
        ((proof_size_gkr + proof_size_pcs) * F::bits()) as f64 / (8.0 * 1024.0),
    );
    println!("Verifier time: {}ms", verifier_duration.as_millis());
}
