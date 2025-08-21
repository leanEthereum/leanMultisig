use p3_field::PrimeCharacteristicRing;
use utils::{
    generate_trace_poseidon_16, generate_trace_poseidon_24, padd_with_zero_to_next_power_of_two,
};
use vm::F;

use crate::execution_trace::{WitnessPoseidon16, WitnessPoseidon24};

pub fn build_poseidon_columns(
    poseidons_16: &[WitnessPoseidon16],
    poseidons_24: &[WitnessPoseidon24],
) -> (Vec<Vec<F>>, Vec<Vec<F>>) {
    let poseidon_16_data = poseidons_16.iter().map(|w| w.input).collect::<Vec<_>>();
    let witness_matrix_poseidon_16 = generate_trace_poseidon_16(poseidon_16_data);
    let poseidon_24_data = poseidons_24.iter().map(|w| w.input).collect::<Vec<_>>();
    let witness_matrix_poseidon_24 = generate_trace_poseidon_24(poseidon_24_data);
    let transposed_16 = witness_matrix_poseidon_16.transpose();
    let cols_16 = transposed_16.row_slices().map(<[F]>::to_vec).collect();
    let transposed_24 = witness_matrix_poseidon_24.transpose();
    let cols_24 = transposed_24.row_slices().map(<[F]>::to_vec).collect();
    (cols_16, cols_24)
}

pub fn all_poseidon_16_indexes(poseidons_16: &[WitnessPoseidon16]) -> Vec<F> {
    padd_with_zero_to_next_power_of_two(
        &[
            poseidons_16
                .iter()
                .map(|p| F::from_usize(p.addr_input_a))
                .collect::<Vec<_>>(),
            poseidons_16
                .iter()
                .map(|p| F::from_usize(p.addr_input_b))
                .collect::<Vec<_>>(),
            poseidons_16
                .iter()
                .map(|p| F::from_usize(p.addr_output))
                .collect::<Vec<_>>(),
        ]
        .concat(),
    )
}

pub fn all_poseidon_24_indexes(poseidons_24: &[WitnessPoseidon24]) -> Vec<F> {
    padd_with_zero_to_next_power_of_two(
        &[
            padd_with_zero_to_next_power_of_two(
                &poseidons_24
                    .iter()
                    .map(|p| F::from_usize(p.addr_input_a))
                    .collect::<Vec<_>>(),
            ),
            padd_with_zero_to_next_power_of_two(
                &poseidons_24
                    .iter()
                    .map(|p| F::from_usize(p.addr_input_b))
                    .collect::<Vec<_>>(),
            ),
            padd_with_zero_to_next_power_of_two(
                &poseidons_24
                    .iter()
                    .map(|p| F::from_usize(p.addr_output))
                    .collect::<Vec<_>>(),
            ),
        ]
        .concat(),
    )
}
