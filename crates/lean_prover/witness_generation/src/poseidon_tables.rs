use std::array;

use lean_vm::{F, PoseidonWitnessTrait, WitnessPoseidon16, WitnessPoseidon24};
use multilinear_toolkit::prelude::*;
use p3_koala_bear::{KoalaBearInternalLayerParameters, KoalaBearParameters};
use p3_monty_31::InternalLayerBaseParameters;
use poseidon_circuit::{PoseidonGKRLayers, PoseidonWitness, generate_poseidon_witness};
use tracing::instrument;
use utils::transposed_par_iter_mut;

pub fn all_poseidon_16_indexes(poseidons_16: &[WitnessPoseidon16]) -> [Vec<F>; 4] {
    assert!(poseidons_16.len().is_power_of_two());
    #[rustfmt::skip]
    let res = [
        poseidons_16.par_iter().map(|p| F::from_usize(p.addr_input_a)).collect::<Vec<_>>(),
        poseidons_16.par_iter().map(|p| F::from_usize(p.addr_input_b)).collect::<Vec<_>>(),
        poseidons_16.par_iter().map(|p| F::from_usize(p.addr_output)).collect::<Vec<_>>(),
        poseidons_16.par_iter().map(|p| {
            F::from_usize((1 - p.is_compression  as usize) * (p.addr_output + 1))
        }).collect::<Vec<_>>(),
    ];
    res
}

pub fn all_poseidon_24_indexes(poseidons_24: &[WitnessPoseidon24]) -> [Vec<F>; 4] {
    assert!(poseidons_24.len().is_power_of_two());
    #[rustfmt::skip]
    let res = [
        poseidons_24.par_iter().map(|p| F::from_usize(p.addr_input_a)).collect::<Vec<_>>(),
        poseidons_24.par_iter().map(|p| F::from_usize(p.addr_input_a + 1)).collect::<Vec<_>>(),
        poseidons_24.par_iter().map(|p| F::from_usize(p.addr_input_b)).collect::<Vec<_>>(),
        poseidons_24.par_iter().map(|p| F::from_usize(p.addr_output)).collect::<Vec<_>>()
    ];
    res
}

#[instrument(skip_all)]
pub fn generate_poseidon_witness_helper<
    const WIDTH: usize,
    const N_COMMITED_CUBES: usize,
    W: PoseidonWitnessTrait<WIDTH> + Send + Sync,
>(
    layers: &PoseidonGKRLayers<WIDTH, N_COMMITED_CUBES>,
    inputs: &[W],
    n_compressions: Option<usize>,
) -> PoseidonWitness<FPacking<F>, WIDTH, N_COMMITED_CUBES>
where
    KoalaBearInternalLayerParameters: InternalLayerBaseParameters<KoalaBearParameters, WIDTH>,
{
    let n_poseidons = inputs.len();
    assert!(n_poseidons.is_power_of_two());
    let mut inputs_transposed: [_; WIDTH] =
        array::from_fn(|_| unsafe { uninitialized_vec(n_poseidons) });
    transposed_par_iter_mut(&mut inputs_transposed)
        .enumerate()
        .for_each(|(i, row)| {
            for (j, p) in row.into_iter().enumerate() {
                *p = inputs[i].inputs()[j];
            }
        });
    let inputs_transposed_packed: [_; WIDTH] =
        array::from_fn(|i| PFPacking::<F>::pack_slice(&inputs_transposed[i]).to_vec()); // TODO avoid cloning
    generate_poseidon_witness::<FPacking<F>, WIDTH, N_COMMITED_CUBES>(
        inputs_transposed_packed,
        layers,
        n_compressions.map(|n_compressions| {
            (
                n_compressions,
                PFPacking::<F>::pack_slice(
                    &[
                        vec![F::ZERO; n_poseidons - n_compressions],
                        vec![F::ONE; n_compressions],
                    ]
                    .concat(),
                )
                .to_vec(),
            )
        }),
    )
}
