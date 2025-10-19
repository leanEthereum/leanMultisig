use lean_vm::{F, WitnessPoseidon16, WitnessPoseidon24};
use p3_field::PrimeCharacteristicRing;
use rayon::prelude::*;
use utils::padd_with_zero_to_next_power_of_two;

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
