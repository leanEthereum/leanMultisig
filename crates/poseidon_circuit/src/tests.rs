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
use whir_p3::precompute_dft_twiddles;

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
const N_COMMITED_CUBES: usize = 16;
const COMPRESSION_OUTPUT_WIDTH: usize = 8;

#[test]
fn test_poseidon_benchmark() {
    run_poseidon_benchmark(8, false);
}

#[test]
fn test_poseidon_compress_benchmark() {
    run_poseidon_benchmark(15, true);
}

fn apply_matrix<const WIDTH: usize, F: Field, EF: ExtensionField<F>>(
    matrix: &[[F; WIDTH]; WIDTH],
    input: &[EF; WIDTH],
) -> [EF; WIDTH] {
    let mut output = [EF::ZERO; WIDTH];
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

pub fn run_poseidon_benchmark(log_n_poseidons: usize, compress: bool) {
    init_tracing();
    precompute_dft_twiddles::<F>(1 << 24);

    let mut rng = StdRng::seed_from_u64(0);
    let n_poseidons = 1 << log_n_poseidons;
    let n_compressions = if compress { n_poseidons / 3 } else { 0 };
    let univariate_skips = UNIVARIATE_SKIPS;
    assert!(univariate_skips <= 4);
    let selectors = univariate_selectors::<F>(univariate_skips);

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

    let mut verifier_state = {
        // ---------------------------------------------------- PROVER ----------------------------------------------------

        let prover_time = Instant::now();

        let mut prover_state = build_prover_state::<EF>();

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

        let mut buff = apply_mds_matrix(&apply_cubes(&initial_layers.last().unwrap()));

        let mut partial_layers = vec![];

        for constant in constants.partial_rounds {
            buff[0] = add_constant(&buff[0], constant);
            partial_layers.push(buff[0].clone());
            buff[0] = cube(&buff[0]);
            buff = apply_light_matrix(&buff);
        }

        let mut final_layers = vec![apply_constants(&buff, &constants.final_full_rounds[0])];
        for constants in &constants.final_full_rounds[1..] {
            final_layers.push(apply_constants(
                &apply_mds_matrix(&apply_cubes(final_layers.last().unwrap())),
                constants,
            ));
        }

        let output = apply_mds_matrix(&apply_cubes(final_layers.last().unwrap()));

        for i in 0..WIDTH {
            // TODO remove
            assert_eq!(
                PFPacking::<EF>::unpack_slice(&output[i]),
                expected_output[i]
            );
        }

        let claim_point = prover_state.sample_vec(log_n_poseidons + 1 - univariate_skips);

        let eq_poly = eval_eq(&claim_point[1..]);
        let output_claims: [_; 16] = info_span!("computing output claims")
            .in_scope(|| {
                output
                    .par_iter()
                    .map(|poly| {
                        evaluate_univariate_multilinear::<_, _, _, false>(
                            FPacking::<F>::unpack_slice(poly),
                            &claim_point,
                            &selectors,
                            Some(&eq_poly),
                        )
                    })
                    .collect::<Vec<_>>()
            })
            .try_into()
            .unwrap();

        prover_state.add_extension_scalars(&output_claims);

        let mut buff = output_claims;
        buff = apply_matrix(&inv_mds_matrix, &buff);

        let (prover_point, buff) = prove_parallel_cubic_sumcheck(
            univariate_skips,
            final_layers
                .last()
                .unwrap()
                .iter()
                .map(Vec::as_slice)
                .collect::<Vec<_>>(),
            claim_point.clone(),
            &mut prover_state,
            buff.to_vec(),
        );
        let mut buff: [EF; WIDTH] = buff.try_into().unwrap();

        for (i, &v) in buff.iter().enumerate() {
            assert_eq!(
                v,
                evaluate_univariate_multilinear::<_, _, _, true>(
                    &PFPacking::<EF>::unpack_slice(&final_layers.last().unwrap()[i]),
                    &prover_point,
                    &selectors,
                    None
                )
            );
        }

        for (i, c) in constants
            .final_full_rounds
            .last()
            .unwrap()
            .iter()
            .enumerate()
        {
            buff[i] -= *c;
        }

        let buff = apply_matrix(&inv_mds_matrix, &buff);

        // let (sc_point, inner_evals, _) = sumcheck_prove(
        //     univariate_skips,
        //     MleGroupRef::BasePacked(vec![&concatenated_cubes]),
        //     &CubeComputation {},
        //     &[],
        //     Some((new_point.clone(), None)),
        //     false,
        //     &mut prover_state,
        //     evaluate_univariate_multilinear::<_, _, _, false>(
        //         &output_claims,
        //         &alpha,
        //         &selectors,
        //         None,
        //     ),
        //     None,
        // );

        // let GKRPoseidonResult {
        //     output_values,
        //     input_statements,
        //     cubes_statements,
        // } = prove_poseidon_gkr(
        //     &mut prover_state,
        //     &witness,
        //     claim_point.clone(),
        //     UNIVARIATE_SKIPS,
        //     &layers,
        // );

        // // PCS opening
        // let mut pcs_statements = vec![];
        // for (point_to_prove, evals_to_prove) in [input_statements, cubes_statements] {
        //     for v in evals_to_prove {
        //         pcs_statements.push(vec![Evaluation {
        //             point: point_to_prove.clone(),
        //             value: v,
        //         }]);
        //     }
        // }

        // let global_statements = packed_pcs_global_statements_for_prover(
        //     &committed_polys,
        //     &committed_col_dims,
        //     log_smallest_decomposition_chunk,
        //     &pcs_statements,
        //     &mut prover_state,
        // );
        // whir_config.prove(
        //     &mut prover_state,
        //     global_statements,
        //     pcs_commitment_witness.inner_witness,
        //     &pcs_commitment_witness.packed_polynomial.by_ref(),
        // );

        // let prover_duration = prover_time.elapsed();

        // (
        //     build_verifier_state(&prover_state),
        //     prover_state.proof_size(),
        //     witness.output_layer,
        //     prover_duration,
        //     output_values,
        //     claim_point,
        // )

        build_verifier_state(&prover_state)
    };

    let verifier_time = Instant::now();

    // let output_values_verifier =
    {
        // ---------------------------------------------------- VERIFIER ----------------------------------------------------

        let output_claim_point = verifier_state.sample_vec(log_n_poseidons);

        //     let GKRPoseidonResult {
        //         output_values,
        //         input_statements,
        //         cubes_statements,
        //     } = verify_poseidon_gkr(
        //         &mut verifier_state,
        //         log_n_poseidons,
        //         &output_claim_point,
        //         &layers,
        //         UNIVARIATE_SKIPS,
        //         if compress { Some(n_compressions) } else { None },
        //     );

        //     // PCS verification
        //     let mut pcs_statements = vec![];
        //     for (point_to_verif, evals_to_verif) in [input_statements, cubes_statements] {
        //         for v in evals_to_verif {
        //             pcs_statements.push(vec![Evaluation {
        //                 point: point_to_verif.clone(),
        //                 value: v,
        //             }]);
        //         }
        //     }

        //     let global_statements = packed_pcs_global_statements_for_verifier(
        //         &committed_col_dims,
        //         log_smallest_decomposition_chunk,
        //         &pcs_statements,
        //         &mut verifier_state,
        //         &Default::default(),
        //     )
        //     .unwrap();

        //     whir_config
        //         .verify::<F>(
        //             &mut verifier_state,
        //             &parsed_pcs_commitment,
        //             global_statements,
        //         )
        //         .unwrap();
        //     output_values
    };
    // let verifier_duration = verifier_time.elapsed();

    // // sanity check: ensure the plaintext poseidons matches the last GKR layer:
    // if compress {
    //     output_layer
    //         .iter()
    //         .enumerate()
    //         .take(COMPRESSION_OUTPUT_WIDTH)
    //         .for_each(|(i, layer)| {
    //             assert_eq!(PFPacking::<EF>::unpack_slice(layer), data_to_hash[i]);
    //         });
    //     output_layer
    //         .iter()
    //         .enumerate()
    //         .skip(COMPRESSION_OUTPUT_WIDTH)
    //         .for_each(|(i, layer)| {
    //             assert_eq!(
    //                 &PFPacking::<EF>::unpack_slice(layer)[..n_poseidons - n_compressions],
    //                 &data_to_hash[i][..n_poseidons - n_compressions]
    //             );
    //             assert!(
    //                 PFPacking::<EF>::unpack_slice(layer)[n_poseidons - n_compressions..]
    //                     .iter()
    //                     .all(|&x| x.is_zero())
    //             );
    //         });
    // } else {
    //     output_layer.iter().enumerate().for_each(|(i, layer)| {
    //         assert_eq!(PFPacking::<EF>::unpack_slice(layer), data_to_hash[i]);
    //     });
    // }
    // assert_eq!(output_values_verifier, output_values_prover);
    // assert_eq!(
    //     output_values_verifier.as_slice(),
    //     &output_layer
    //         .iter()
    //         .map(|layer| PFPacking::<EF>::unpack_slice(layer)
    //             .evaluate(&MultilinearPoint(claim_point.clone())))
    //         .collect::<Vec<_>>()
    // );

    // println!("2^{} Poseidon2", log_n_poseidons);
    // println!(
    //     "Plaintext (no proof) time: {:.3}s ({:.2}M Poseidons / s)",
    //     plaintext_duration.as_secs_f64(),
    //     n_poseidons as f64 / (plaintext_duration.as_secs_f64() * 1e6)
    // );
    // println!(
    //     "Prover time: {:.3}s ({:.2}M Poseidons / s, {:.1}x slower than plaintext)",
    //     prover_duration.as_secs_f64(),
    //     n_poseidons as f64 / (prover_duration.as_secs_f64() * 1e6),
    //     prover_duration.as_secs_f64() / plaintext_duration.as_secs_f64()
    // );
    // println!(
    //     "Proof size: {:.1} KiB (without merkle pruning)",
    //     (proof_size * F::bits()) as f64 / (8.0 * 1024.0)
    // );
    // println!("Verifier time: {}ms", verifier_duration.as_millis());
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
            assert_eq!(vector, recovered);
        }
    }

    #[test]
    fn test_cube_sumcheck() {
        let univariate_skips = 3;
        let n_polys = 16;
        let n_vars = 13;
        let selectors = univariate_selectors::<F>(univariate_skips);

        let mut rng = StdRng::seed_from_u64(0);

        let polys = (0..n_polys)
            .map(|_| (0..1 << n_vars).map(|_| rng.random()).collect::<Vec<F>>())
            .collect::<Vec<_>>();

        let cubes = polys
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

        let (prover_point, prover_inner_values) = prove_parallel_cubic_sumcheck(
            univariate_skips,
            polys
                .iter()
                .map(|poly| FPacking::<F>::pack_slice(poly))
                .collect(),
            eq_point.clone(),
            &mut prover_state,
            claimed_cube_values.clone(),
        );

        let mut verifier_state = build_verifier_state(&prover_state);

        let (verifier_point, verifier_inner_values) = verify_parallel_cubic_sumcheck(
            &mut verifier_state,
            univariate_skips,
            &eq_point,
            claimed_cube_values,
        )
        .unwrap();

        assert_eq!(&prover_point.0, &verifier_point);
        assert_eq!(prover_inner_values, verifier_inner_values);

        for i in 0..n_polys {
            assert_eq!(
                evaluate_univariate_multilinear::<_, _, _, true>(
                    &polys[i],
                    &prover_point,
                    &selectors,
                    None,
                ),
                prover_inner_values[i]
            );
        }
    }
}
