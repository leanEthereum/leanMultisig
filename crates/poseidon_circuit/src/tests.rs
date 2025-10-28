use multilinear_toolkit::prelude::*;
use p3_koala_bear::{GenericPoseidon2LinearLayersKoalaBear, KoalaBear, QuinticExtensionFieldKB};
use p3_poseidon2::GenericPoseidon2LinearLayers;

use rand::{Rng, SeedableRng, rngs::StdRng};
use std::{array, time::Instant};
use tracing::info_span;
use utils::{
    build_prover_state, build_verifier_state, init_tracing, poseidon16_permute_mut,
    poseidon24_permute_mut, transposed_par_iter_mut,
};
use whir_p3::{
    FoldingFactor, SecurityAssumption, WhirConfig, WhirConfigBuilder, precompute_dft_twiddles,
};

use p3_koala_bear::{
    KOALABEAR_RC16_EXTERNAL_FINAL, KOALABEAR_RC16_EXTERNAL_INITIAL, KOALABEAR_RC16_INTERNAL,
};

use crate::{
    RoundConstants, add_constant, apply_constants, apply_cubes, apply_light_matrix,
    apply_mds_matrix, cube,
};

type F = KoalaBear;
type EF = QuinticExtensionFieldKB;

const WIDTH: usize = 16;

const UNIVARIATE_SKIPS: usize = 3;
const COMPRESSION_OUTPUT_WIDTH: usize = 8;

#[test]
fn test_poseidon_benchmark() {
    run_poseidon_benchmark(20);
}

fn apply_matrix<const WIDTH: usize, F: Field, EF: ExtensionField<F>>(
    matrix: &[[F; WIDTH]; WIDTH],
    input: &[EF],
) -> Vec<EF> {
    assert_eq!(input.len(), WIDTH);
    let mut output = EF::zero_vec(WIDTH);
    for i in 0..WIDTH {
        for j in 0..WIDTH {
            output[i] += input[j] * matrix[i][j];
        }
    }
    output
}

fn transpose_matrix<const WIDTH: usize, F: Field>(
    matrix: &[[F; WIDTH]; WIDTH],
) -> [[F; WIDTH]; WIDTH] {
    let mut transposed = [[F::ZERO; WIDTH]; WIDTH];
    for i in 0..WIDTH {
        for j in 0..WIDTH {
            transposed[j][i] = matrix[i][j];
        }
    }
    transposed
}

fn inverse_matrix<const WIDTH: usize, F: Field>(
    matrix: &[[F; WIDTH]; WIDTH],
) -> [[F; WIDTH]; WIDTH] {
    // Create an augmented matrix [A | I]
    let mut augmented: Vec<Vec<F>> = vec![vec![F::ZERO; WIDTH * 2]; WIDTH];

    for i in 0..WIDTH {
        for j in 0..WIDTH {
            augmented[i][j] = matrix[i][j];
        }
        augmented[i][WIDTH + i] = F::ONE;
    }

    // Forward elimination with partial pivoting
    for col in 0..WIDTH {
        // Find pivot
        let mut pivot_row = col;
        for i in (col + 1)..WIDTH {
            if augmented[i][col] != F::ZERO {
                pivot_row = i;
                break;
            }
        }

        // Swap rows if needed
        if pivot_row != col {
            augmented.swap(col, pivot_row);
        }

        // Scale pivot row
        let pivot = augmented[col][col];
        assert!(pivot != F::ZERO, "Matrix is singular");

        let pivot_inv = pivot.inverse();
        for j in 0..(WIDTH * 2) {
            augmented[col][j] *= pivot_inv;
        }

        // Eliminate column in other rows
        for i in 0..WIDTH {
            if i != col {
                let factor = augmented[i][col];
                let col_row = augmented[col].clone();
                for j in 0..(WIDTH * 2) {
                    augmented[i][j] -= factor * col_row[j];
                }
            }
        }
    }

    // Extract the inverse matrix from the right side
    let mut inverse = [[F::ZERO; WIDTH]; WIDTH];
    for i in 0..WIDTH {
        for j in 0..WIDTH {
            inverse[i][j] = augmented[i][WIDTH + j];
        }
    }

    inverse
}

pub fn run_poseidon_benchmark(log_n_poseidons: usize) {
    init_tracing();
    precompute_dft_twiddles::<F>(1 << 24);

    let mut rng = StdRng::seed_from_u64(0);
    let n_poseidons = 1 << log_n_poseidons;
    let univariate_skips = UNIVARIATE_SKIPS;
    assert!(univariate_skips <= 4);
    let selectors = univariate_selectors::<F>(univariate_skips);
    let whir_config_builder = WhirConfigBuilder {
        folding_factor: FoldingFactor::new(7, 4),
        soundness_type: SecurityAssumption::CapacityBound,
        pow_bits: WIDTH,
        max_num_variables_to_send_coeffs: 6,
        rs_domain_initial_reduction_factor: 5,
        security_level: 128,
        starting_log_inv_rate: 1,
    };
    let whir_n_vars = log_n_poseidons + log2_strict_usize(WIDTH);
    let whir_config = WhirConfig::new(whir_config_builder, whir_n_vars);

    let mut mds_matrix: [[F; WIDTH]; WIDTH] = Default::default();
    for i in 0..WIDTH {
        mds_matrix[i][i] = F::ONE;
        GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(&mut mds_matrix[i]);
    }
    mds_matrix = transpose_matrix(&mds_matrix);
    let inv_mds_matrix = inverse_matrix(&mds_matrix);

    let mut light_matrix: [[F; WIDTH]; WIDTH] = Default::default();
    for i in 0..WIDTH {
        light_matrix[i][i] = F::ONE;
        GenericPoseidon2LinearLayersKoalaBear::internal_linear_layer(&mut light_matrix[i]);
    }
    light_matrix = transpose_matrix(&light_matrix);
    let inv_light_matrix = inverse_matrix(&light_matrix);

    let perm_inputs = (0..n_poseidons)
        .map(|_| rng.random())
        .collect::<Vec<[F; WIDTH]>>();
    let input: [_; WIDTH] =
        array::from_fn(|i| perm_inputs.par_iter().map(|x| x[i]).collect::<Vec<F>>());
    let input_packed: [_; WIDTH] =
        array::from_fn(|i| PFPacking::<EF>::pack_slice(&input[i]).to_vec());

    let mut expected_output = input.clone();
    let plaintext_time = Instant::now();
    transposed_par_iter_mut(&mut expected_output).for_each(|row| {
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

    let constants = RoundConstants {
        initial_full_rounds: KOALABEAR_RC16_EXTERNAL_INITIAL.to_vec(),
        partial_rounds: KOALABEAR_RC16_INTERNAL.to_vec(),
        final_full_rounds: KOALABEAR_RC16_EXTERNAL_FINAL.to_vec(),
    };

    // let (
    //     mut verifier_state,
    //     proof_size,
    //     output_layer,
    //     prover_duration,
    //     output_values_prover,
    //     claim_point,
    // ) =

    let prover_time = Instant::now();

    let (mut verifier_state, output, proof_size) = {
        // ---------------------------------------------------- PROVER ----------------------------------------------------

        let mut prover_state = build_prover_state::<EF>();

        // PCS commitment
        let mut global_poly_commited: Vec<F> = unsafe { uninitialized_vec(1 << whir_n_vars) };
        let mut chunks = split_at_mut_many(
            &mut global_poly_commited,
            (0..WIDTH)
                .map(|i| (i + 1) << log_n_poseidons)
                .collect::<Vec<_>>()
                .as_slice(),
        );
        chunks[..WIDTH]
            .par_iter_mut()
            .enumerate()
            .for_each(|(i, chunk)| {
                chunk.copy_from_slice(&input[i]);
            });

        let global_poly_commited = MleOwned::Base(global_poly_commited);
        let pcs_witness = whir_config.commit(&mut prover_state, &global_poly_commited);
        let global_poly_commited_packed =
            PFPacking::<EF>::pack_slice(global_poly_commited.as_base().unwrap());

        let mut initial_layers = vec![];
        initial_layers.push(apply_constants(
            &apply_mds_matrix(&input_packed),
            &constants.initial_full_rounds[0],
        ));
        for constants in &constants.initial_full_rounds[1..] {
            initial_layers.push(apply_constants(
                &apply_mds_matrix(&apply_cubes(&&initial_layers.last().unwrap())),
                constants,
            ));
        }

        let mut buff_layer = apply_mds_matrix(&apply_cubes(&initial_layers.last().unwrap()));

        let mut partial_layers = vec![];

        for constant in &constants.partial_rounds {
            buff_layer[0] = add_constant(&buff_layer[0], *constant);
            partial_layers.push(buff_layer.clone());
            buff_layer[0] = cube(&buff_layer[0]);
            buff_layer = apply_light_matrix(&buff_layer);
        }

        let mut final_layers = vec![apply_constants(
            &buff_layer,
            &constants.final_full_rounds[0],
        )];
        for constants in &constants.final_full_rounds[1..] {
            final_layers.push(apply_constants(
                &apply_mds_matrix(&apply_cubes(final_layers.last().unwrap())),
                constants,
            ));
        }

        let output = apply_mds_matrix(&apply_cubes(final_layers.last().unwrap()));

        let mut point = prover_state.sample_vec(log_n_poseidons + 1 - univariate_skips);

        let eq_poly = eval_eq(&point[1..]);
        let output_claims = info_span!("computing output claims").in_scope(|| {
            output
                .par_iter()
                .map(|poly| {
                    evaluate_univariate_multilinear::<_, _, _, false>(
                        FPacking::<F>::unpack_slice(poly),
                        &point,
                        &selectors,
                        Some(&eq_poly),
                    )
                })
                .collect::<Vec<_>>()
        });

        prover_state.add_extension_scalars(&output_claims);

        let mut buff = output_claims;

        for (constants, layer) in constants.final_full_rounds.iter().zip(&final_layers).rev() {
            buff = apply_matrix(&inv_mds_matrix, &buff);

            (point, buff) = prove_poseidon_gkr_sumcheck(
                univariate_skips,
                layer.iter().map(Vec::as_slice).collect::<Vec<_>>(),
                point.clone(),
                &mut prover_state,
                &buff,
                WIDTH,
            );

            for (i, c) in constants.iter().enumerate() {
                buff[i] -= *c;
            }
        }

        for (constant, layer) in constants.partial_rounds.iter().zip(&partial_layers).rev() {
            buff = apply_matrix(&inv_light_matrix, &buff);

            (point, buff) = prove_poseidon_gkr_sumcheck(
                univariate_skips,
                layer.iter().map(Vec::as_slice).collect::<Vec<_>>(),
                point.clone(),
                &mut prover_state,
                &buff,
                1,
            );

            buff[0] -= *constant;
        }

        for (constants, layer) in constants
            .initial_full_rounds
            .iter()
            .zip(&initial_layers)
            .rev()
        {
            buff = apply_matrix(&inv_mds_matrix, &buff);

            (point, buff) = prove_poseidon_gkr_sumcheck(
                univariate_skips,
                layer.iter().map(Vec::as_slice).collect::<Vec<_>>(),
                point.clone(),
                &mut prover_state,
                &buff,
                WIDTH,
            );

            for (i, c) in constants.iter().enumerate() {
                buff[i] -= *c;
            }
        }

        buff = apply_matrix(&inv_mds_matrix, &buff);

        for i in 0..WIDTH {
            assert_eq!(
                evaluate_univariate_multilinear::<_, _, _, false>(
                    &input[i], &point, &selectors, None
                ),
                buff[i]
            );
        }

        // PCS opening

        let eq_mle_inputs = eval_eq_packed(&point[1..]);
        let inner_evals_inputs = global_poly_commited_packed
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
        let inner_evals = prover_state.sample_vec(log2_strict_usize(WIDTH) + UNIVARIATE_SKIPS);
        let pcs_statements = vec![Evaluation {
            point: MultilinearPoint([inner_evals.clone(), point[1..].to_vec()].concat()),
            value: inner_evals_inputs.evaluate(&MultilinearPoint(inner_evals)),
        }];

        whir_config.prove(
            &mut prover_state,
            pcs_statements,
            pcs_witness,
            &global_poly_commited.by_ref(),
        );

        (
            build_verifier_state(&prover_state),
            output,
            prover_state.proof_size(),
        )
    };
    let prover_duration = prover_time.elapsed();

    let verifier_time = Instant::now();

    {
        // ---------------------------------------------------- VERIFIER ----------------------------------------------------

        let parsed_pcs_commitment = whir_config
            .parse_commitment::<F>(&mut verifier_state)
            .unwrap();

        let mut point = verifier_state.sample_vec(log_n_poseidons + 1 - univariate_skips);
        let mut buff = verifier_state.next_extension_scalars_vec(WIDTH).unwrap();

        for constants in constants.final_full_rounds.iter().rev() {
            buff = apply_matrix(&inv_mds_matrix, &buff);

            (point, buff) = verify_poseidon_gkr_sumcheck(
                &mut verifier_state,
                univariate_skips,
                &point,
                &buff,
                WIDTH,
                0,
            )
            .unwrap();

            for (i, c) in constants.iter().enumerate() {
                buff[i] -= *c;
            }
        }

        for constant in constants.partial_rounds.iter().rev() {
            buff = apply_matrix(&inv_light_matrix, &buff);

            (point, buff) = verify_poseidon_gkr_sumcheck(
                &mut verifier_state,
                univariate_skips,
                &point,
                &buff,
                1,
                WIDTH - 1,
            )
            .unwrap();
            buff[0] -= *constant;
        }

        for constants in constants.initial_full_rounds.iter().rev() {
            buff = apply_matrix(&inv_mds_matrix, &buff);

            (point, buff) = verify_poseidon_gkr_sumcheck(
                &mut verifier_state,
                univariate_skips,
                &point,
                &buff,
                WIDTH,
                0,
            )
            .unwrap();

            for (i, c) in constants.iter().enumerate() {
                buff[i] -= *c;
            }
        }

        buff = apply_matrix(&inv_mds_matrix, &buff);

        let inner_evals_inputs = verifier_state
            .next_extension_scalars_vec(WIDTH << UNIVARIATE_SKIPS)
            .unwrap();
        let inner_evals = verifier_state.sample_vec(log2_strict_usize(WIDTH) + UNIVARIATE_SKIPS);
        let pcs_statements = vec![Evaluation {
            point: MultilinearPoint([inner_evals.clone(), point[1..].to_vec()].concat()),
            value: inner_evals_inputs.evaluate(&MultilinearPoint(inner_evals)),
        }];
        {
            for (&eval, inner_evals) in buff
                .iter()
                .zip(inner_evals_inputs.chunks_exact(1 << UNIVARIATE_SKIPS))
            {
                assert_eq!(
                    eval,
                    evaluate_univariate_multilinear::<_, _, _, false>(
                        inner_evals,
                        &point[..1],
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

    // sanity check: ensure the plaintext poseidons matches the last GKR layer:
    assert_eq!(
        output
            .iter()
            .map(|layer| PFPacking::<EF>::unpack_slice(layer))
            .collect::<Vec<_>>(),
        expected_output
    );

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

#[cfg(test)]
mod tests {
    use super::*;
    use p3_field::PrimeCharacteristicRing;
    use rand::{SeedableRng, rngs::StdRng};

    #[test]
    fn test_inverse_matrix() {
        let mut rng = StdRng::seed_from_u64(0);
        for _ in 0..100 {
            let matrix: [[F; WIDTH]; WIDTH] = array::from_fn(|_| array::from_fn(|_| rng.random()));
            let inv_matrix = inverse_matrix(&matrix);
            let vector: [F; WIDTH] = array::from_fn(|_| rng.random());
            let transformed = apply_matrix(&matrix, &vector);
            let recovered = apply_matrix(&inv_matrix, &transformed);
            assert_eq!(vector.to_vec(), recovered);
        }
    }

    #[test]
    fn test_cube_sumcheck() {
        let univariate_skips = 3;
        let n_cubes = 3;
        let n_transparents = 5;
        let n_vars = 13;
        let selectors = univariate_selectors::<F>(univariate_skips);

        let mut rng = StdRng::seed_from_u64(0);

        let polys_to_cube = (0..n_cubes)
            .map(|_| (0..1 << n_vars).map(|_| rng.random()).collect::<Vec<F>>())
            .collect::<Vec<_>>();
        let transparent_polys = (0..n_transparents)
            .map(|_| (0..1 << n_vars).map(|_| rng.random()).collect::<Vec<F>>())
            .collect::<Vec<_>>();

        let cubes = polys_to_cube
            .iter()
            .map(|p| p.par_iter().map(|&x| x.cube()).collect::<Vec<_>>())
            .collect::<Vec<_>>();

        let mut prover_state = build_prover_state::<EF>();

        let eq_point = (0..n_vars + 1 - univariate_skips)
            .map(|_| rng.random())
            .collect::<Vec<EF>>();

        let claimed_cube_values = cubes
            .iter()
            .map(|c| {
                evaluate_univariate_multilinear::<_, _, _, true>(
                    c,
                    &MultilinearPoint(eq_point.clone()),
                    &selectors,
                    None,
                )
            })
            .collect::<Vec<_>>();

        let claimed_transparent_evals = transparent_polys
            .iter()
            .map(|p| {
                evaluate_univariate_multilinear::<_, _, _, true>(
                    p,
                    &MultilinearPoint(eq_point.clone()),
                    &selectors,
                    None,
                )
            })
            .collect::<Vec<_>>();

        let (prover_point, next_evals_prover) = prove_poseidon_gkr_sumcheck(
            univariate_skips,
            polys_to_cube
                .iter()
                .chain(transparent_polys.iter())
                .map(|poly| FPacking::<F>::pack_slice(poly))
                .collect(),
            eq_point.clone(),
            &mut prover_state,
            &[
                claimed_cube_values.clone(),
                claimed_transparent_evals.clone(),
            ]
            .concat(),
            n_cubes,
        );

        let mut verifier_state = build_verifier_state(&prover_state);

        let (verifier_point, next_evals_verifier) = verify_poseidon_gkr_sumcheck(
            &mut verifier_state,
            univariate_skips,
            &eq_point,
            &[
                claimed_cube_values.clone(),
                claimed_transparent_evals.clone(),
            ]
            .concat(),
            n_cubes,
            n_transparents,
        )
        .unwrap();

        assert_eq!(&prover_point, &verifier_point);
        assert_eq!(&next_evals_prover, &next_evals_verifier);

        for i in 0..n_cubes {
            assert_eq!(
                evaluate_univariate_multilinear::<_, _, _, true>(
                    &polys_to_cube[i],
                    &prover_point,
                    &selectors,
                    None,
                ),
                next_evals_prover[i]
            );
        }
        for i in 0..n_transparents {
            assert_eq!(
                evaluate_univariate_multilinear::<_, _, _, true>(
                    &transparent_polys[i],
                    &prover_point,
                    &selectors,
                    None,
                ),
                next_evals_prover[i + n_cubes]
            );
        }
    }
}
