use lean_vm::{F, WitnessPoseidon16, WitnessPoseidon24};
use p3_field::PrimeCharacteristicRing;
use rayon::prelude::*;
use utils::{
    generate_trace_poseidon_16, generate_trace_poseidon_24, padd_with_zero_to_next_power_of_two,
};

#[inline]
pub fn build_poseidon_columns(
    poseidons_16: &[WitnessPoseidon16],
    poseidons_24: &[WitnessPoseidon24],
) -> (Vec<Vec<F>>, Vec<Vec<F>>) {
    rayon::join(
        || {
            let inputs = poseidons_16.par_iter().map(|w| w.input).collect();
            let matrix = generate_trace_poseidon_16(inputs);
            matrix.transpose().row_slices().map(<[F]>::to_vec).collect()
        },
        || {
            let inputs = poseidons_24.par_iter().map(|w| w.input).collect();
            let matrix = generate_trace_poseidon_24(inputs);
            matrix.transpose().row_slices().map(<[F]>::to_vec).collect()
        },
    )
}

#[inline]
pub fn all_poseidon_16_indexes(poseidons_16: &[WitnessPoseidon16]) -> [Vec<F>; 3] {
    let ((addr_a, addr_b), addr_c) = rayon::join(
        || {
            rayon::join(
                || {
                    poseidons_16
                        .par_iter()
                        .map(|p| F::from_usize(p.addr_input_a))
                        .collect()
                },
                || {
                    poseidons_16
                        .par_iter()
                        .map(|p| F::from_usize(p.addr_input_b))
                        .collect()
                },
            )
        },
        || {
            poseidons_16
                .par_iter()
                .map(|p| F::from_usize(p.addr_output))
                .collect()
        },
    );
    [addr_a, addr_b, addr_c]
}

#[inline]
pub fn all_poseidon_24_indexes(poseidons_24: &[WitnessPoseidon24]) -> [Vec<F>; 3] {
    let ((temp_a, temp_b), temp_c) = rayon::join(
        || {
            rayon::join(
                || {
                    poseidons_24
                        .par_iter()
                        .map(|p| F::from_usize(p.addr_input_a))
                        .collect::<Vec<F>>()
                },
                || {
                    poseidons_24
                        .par_iter()
                        .map(|p| F::from_usize(p.addr_input_b))
                        .collect::<Vec<F>>()
                },
            )
        },
        || {
            poseidons_24
                .par_iter()
                .map(|p| F::from_usize(p.addr_output))
                .collect::<Vec<F>>()
        },
    );

    let ((padded_a, padded_b), padded_c) = rayon::join(
        || {
            rayon::join(
                || padd_with_zero_to_next_power_of_two(&temp_a),
                || padd_with_zero_to_next_power_of_two(&temp_b),
            )
        },
        || padd_with_zero_to_next_power_of_two(&temp_c),
    );

    [padded_a, padded_b, padded_c]
}

#[inline]
pub fn full_poseidon_indexes_poly(
    poseidons_16: &[WitnessPoseidon16],
    poseidons_24: &[WitnessPoseidon24],
) -> Vec<F> {
    let max_n = poseidons_16
        .len()
        .max(poseidons_24.len())
        .next_power_of_two();

    // Generate all chunks in parallel
    let (chunks_16, chunks_24) = rayon::join(
        || {
            // Generate 4 chunks for poseidon_16 in parallel
            let ((chunk0, chunk1), (chunk2, chunk3)) = rayon::join(
                || {
                    rayon::join(
                        || {
                            poseidons_16
                                .par_iter()
                                .map(|p| p.addr_input_a)
                                .collect::<Vec<_>>()
                        },
                        || {
                            poseidons_16
                                .par_iter()
                                .map(|p| p.addr_input_b)
                                .collect::<Vec<_>>()
                        },
                    )
                },
                || {
                    rayon::join(
                        || {
                            poseidons_16
                                .par_iter()
                                .map(|p| p.addr_output)
                                .collect::<Vec<_>>()
                        },
                        || {
                            poseidons_16
                                .par_iter()
                                .map(|p| p.addr_output + 1)
                                .collect::<Vec<_>>()
                        },
                    )
                },
            );
            [chunk0, chunk1, chunk2, chunk3]
        },
        || {
            // Generate 4 chunks for poseidon_24 in parallel
            let ((chunk0, chunk1), (chunk2, chunk3)) = rayon::join(
                || {
                    rayon::join(
                        || {
                            poseidons_24
                                .par_iter()
                                .map(|p| p.addr_input_a)
                                .collect::<Vec<_>>()
                        },
                        || {
                            poseidons_24
                                .par_iter()
                                .map(|p| p.addr_input_a + 1)
                                .collect::<Vec<_>>()
                        },
                    )
                },
                || {
                    rayon::join(
                        || {
                            poseidons_24
                                .par_iter()
                                .map(|p| p.addr_input_b)
                                .collect::<Vec<_>>()
                        },
                        || {
                            poseidons_24
                                .par_iter()
                                .map(|p| p.addr_output)
                                .collect::<Vec<_>>()
                        },
                    )
                },
            );
            [chunk0, chunk1, chunk2, chunk3]
        },
    );

    // Combine all chunks efficiently
    let mut result = F::zero_vec(8 * max_n);

    // Fill the result vector in parallel chunks
    result
        .par_chunks_mut(max_n)
        .enumerate()
        .for_each(|(chunk_idx, chunk)| {
            if chunk_idx < 4 {
                // Poseidon16 chunks
                chunk[..chunks_16[chunk_idx].len()]
                    .par_iter_mut()
                    .zip(chunks_16[chunk_idx].par_iter())
                    .for_each(|(slot, &addr)| *slot = F::from_usize(addr));
            } else if chunk_idx < 8 {
                // Poseidon24 chunks
                let idx = chunk_idx - 4;
                chunk[..chunks_24[idx].len()]
                    .par_iter_mut()
                    .zip(chunks_24[idx].par_iter())
                    .for_each(|(slot, &addr)| *slot = F::from_usize(addr));
            }
        });

    result
}
