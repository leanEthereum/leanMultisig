use p3_field::PrimeCharacteristicRing;

use crate::{
    constant::F,
    poseidon2::{generate_trace_poseidon_16, generate_trace_poseidon_24},
    utils::pad_to_power_of_two,
    witness::poseidon::{WitnessPoseidon16, WitnessPoseidon24},
};

/// Build Poseidon Columns
///
/// This function generates the execution traces for both Poseidon16 and Poseidon24 operations.
///
/// ## Arguments
/// * `poseidons_16`: A slice of `WitnessPoseidon16` structs.
/// * `poseidons_24`: A slice of `WitnessPoseidon24` structs.
///
/// ## Returns
/// A tuple containing two items:
/// 1. A `Vec<Vec<F>>` for the Poseidon16 trace, where each inner vector is a column.
/// 2. A `Vec<Vec<F>>` for the Poseidon24 trace, where each inner vector is a column.
pub fn build_poseidon_columns(
    poseidons_16: &[WitnessPoseidon16],
    poseidons_24: &[WitnessPoseidon24],
) -> (Vec<Vec<F>>, Vec<Vec<F>>) {
    // Poseidon16 Trace Generation
    //
    // Extract the `input` state from each Poseidon16 witness.
    let poseidon_16_data = poseidons_16.iter().map(|w| w.input).collect::<Vec<_>>();
    // Generate the full execution trace for all Poseidon16 operations.
    // This returns a `RowMajorMatrix`.
    let witness_matrix_poseidon_16 = generate_trace_poseidon_16(poseidon_16_data);

    // Poseidon24 Trace Generation
    //
    // Extract the `input` state from each Poseidon24 witness.
    let poseidon_24_data = poseidons_24.iter().map(|w| w.input).collect::<Vec<_>>();
    // Generate the full execution trace for all Poseidon24 operations.
    let witness_matrix_poseidon_24 = generate_trace_poseidon_24(poseidon_24_data);

    // Column Extraction
    //
    // To get the columns of a row-major matrix, we first transpose it.
    let transposed_16 = witness_matrix_poseidon_16.transpose();
    // After transposing, the rows of the new matrix are the columns of the original.
    // We can then iterate over the row slices of the transposed matrix and collect them.
    let cols_16 = transposed_16.row_slices().map(<[F]>::to_vec).collect();

    // Repeat the same process for the Poseidon24 trace.
    let transposed_24 = witness_matrix_poseidon_24.transpose();
    let cols_24 = transposed_24.row_slices().map(<[F]>::to_vec).collect();

    // Return the two sets of columns.
    (cols_16, cols_24)
}

/// All Poseidon16 Indexes
///
/// This function collects all memory addresses used by the Poseidon16 precompile,
/// flattens them into a single vector, and pads it to the next power of two.
///
/// ## Arguments
/// * `poseidons_16`: A slice of `WitnessPoseidon16` structs.
///
/// ## Returns
/// A padded `Vec<F>` containing the concatenated offsets of `addr_input_a`, `addr_input_b`, and `addr_output`.
#[must_use]
pub fn all_poseidon_16_indexes(poseidons_16: &[WitnessPoseidon16]) -> Vec<F> {
    // Collect all the indices into a single vector.
    let all_indices: Vec<F> = poseidons_16
        .iter()
        .map(|p| F::from_usize(p.addr_input_a.offset))
        .chain(
            poseidons_16
                .iter()
                .map(|p| F::from_usize(p.addr_input_b.offset)),
        )
        .chain(
            poseidons_16
                .iter()
                .map(|p| F::from_usize(p.addr_output.offset)),
        )
        .collect();

    // Pad the final vector with zeros to the next power of two.
    pad_to_power_of_two(&all_indices)
}

/// All Poseidon24 Indexes
///
/// This function collects all memory addresses used by the Poseidon24 precompile,
/// flattens them into a single vector, and pads it to the next power of two.
///
/// ## Arguments
/// * `poseidons_24`: A slice of `WitnessPoseidon24` structs.
///
/// ## Returns
/// A padded `Vec<F>` containing the concatenated and individually padded offsets of
/// `addr_input_a`, `addr_input_b`, and `addr_output`.
#[must_use]
pub fn all_poseidon_24_indexes(poseidons_24: &[WitnessPoseidon24]) -> Vec<F> {
    // Extract and pad the offsets for `addr_input_a`.
    let indices_a = pad_to_power_of_two(
        &poseidons_24
            .iter()
            .map(|p| F::from_usize(p.addr_input_a.offset))
            .collect::<Vec<_>>(),
    );
    // Extract and pad the offsets for `addr_input_b`.
    let indices_b = pad_to_power_of_two(
        &poseidons_24
            .iter()
            .map(|p| F::from_usize(p.addr_input_b.offset))
            .collect::<Vec<_>>(),
    );
    // Extract and pad the offsets for `addr_output`.
    let indices_c = pad_to_power_of_two(
        &poseidons_24
            .iter()
            .map(|p| F::from_usize(p.addr_output.offset))
            .collect::<Vec<_>>(),
    );

    // Concatenate the three padded vectors into a single flat vector.
    [indices_a, indices_b, indices_c].concat()
}
