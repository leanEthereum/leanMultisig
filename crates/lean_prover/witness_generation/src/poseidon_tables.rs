use lean_vm::{
    F, POSEIDON_16_DEFAULT_COMPRESSION, POSEIDON_16_NULL_HASH_PTR, WitnessPoseidon16,
    WitnessPoseidon24,
};
use p3_field::PrimeCharacteristicRing;
use rayon::prelude::*;
use tracing::instrument;
use utils::{
    POSEIDON16_AIR_N_COLS, POSEIDON24_AIR_N_COLS, default_poseidon16_air_row,
    default_poseidon24_air_row, generate_trace_poseidon_16, generate_trace_poseidon_24,
    padd_with_zero_to_next_power_of_two,
};

#[instrument(skip_all)]
pub fn build_poseidon_24_columns(
    poseidons_24: &[WitnessPoseidon24],
    padding: usize,
) -> Vec<Vec<F>> {
    let inputs = poseidons_24.par_iter().map(|w| w.input).collect::<Vec<_>>();
    let matrix = generate_trace_poseidon_24(&inputs);
    let mut res = utils::transpose(&matrix.values, POSEIDON24_AIR_N_COLS, padding);
    let default_p24_row = default_poseidon24_air_row();
    assert_eq!(default_p24_row.len(), res.len());
    res.par_iter_mut()
        .zip(default_p24_row.par_iter())
        .for_each(|(col, default_value)| {
            col.resize(col.len() + padding, *default_value);
        });
    res
}

#[instrument(skip_all)]
pub fn build_poseidon_16_columns(
    poseidons_16: &[WitnessPoseidon16],
    padding: usize,
) -> Vec<Vec<F>> {
    let inputs = poseidons_16.par_iter().map(|w| w.input).collect::<Vec<_>>();
    let compresses = poseidons_16
        .par_iter()
        .map(|w| w.is_compression)
        .collect::<Vec<_>>();
    let index_res = poseidons_16
        .par_iter()
        .map(|w| w.addr_output)
        .collect::<Vec<_>>();
    let matrix = generate_trace_poseidon_16(&inputs, &compresses, &index_res);
    let mut res = utils::transpose(&matrix.values, POSEIDON16_AIR_N_COLS, padding);

    let default_p16_row =
        default_poseidon16_air_row(POSEIDON_16_DEFAULT_COMPRESSION, POSEIDON_16_NULL_HASH_PTR);
    assert_eq!(default_p16_row.len(), res.len());
    res.par_iter_mut()
        .zip(default_p16_row.par_iter())
        .for_each(|(col, default_value)| {
            col.resize(col.len() + padding, *default_value);
        });
    res
}

pub fn all_poseidon_16_indexes_input(poseidons_16: &[WitnessPoseidon16]) -> [Vec<F>; 2] {
    [
        poseidons_16
            .par_iter()
            .map(|p| F::from_usize(p.addr_input_a))
            .collect::<Vec<_>>(),
        poseidons_16
            .par_iter()
            .map(|p| F::from_usize(p.addr_input_b))
            .collect::<Vec<_>>(),
    ]
}

pub fn all_poseidon_24_indexes(poseidons_24: &[WitnessPoseidon24]) -> [Vec<F>; 3] {
    [
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
}

pub fn full_poseidon_indexes_poly(
    poseidons_16: &[WitnessPoseidon16],
    poseidons_24: &[WitnessPoseidon24],
) -> Vec<F> {
    let max_n_poseidons = poseidons_16
        .len()
        .max(poseidons_24.len())
        .next_power_of_two();
    let mut all_poseidon_indexes = F::zero_vec(8 * max_n_poseidons);
    #[rustfmt::skip]
        let chunks = [
            poseidons_16.par_iter().map(|p| p.addr_input_a).collect::<Vec<_>>(),
            poseidons_16.par_iter().map(|p| p.addr_input_b).collect::<Vec<_>>(),
            poseidons_16.par_iter().map(|p| p.addr_output).collect::<Vec<_>>(),
            poseidons_16.par_iter().map(|p| {
                if p.is_compression { 0 } else { p.addr_output + 1 }
            })
            .collect::<Vec<_>>(),
            poseidons_24.par_iter().map(|p| p.addr_input_a).collect::<Vec<_>>(),
            poseidons_24.par_iter().map(|p| p.addr_input_a + 1).collect::<Vec<_>>(),
            poseidons_24.par_iter().map(|p| p.addr_input_b).collect::<Vec<_>>(),
            poseidons_24.par_iter().map(|p| p.addr_output).collect::<Vec<_>>()
        ];

    for (chunk_idx, addrs) in chunks.into_iter().enumerate() {
        all_poseidon_indexes[chunk_idx * max_n_poseidons..]
            .par_iter_mut()
            .zip(addrs)
            .for_each(|(slot, addr)| {
                *slot = F::from_usize(addr);
            });
    }

    all_poseidon_indexes
}
