use std::array;

use lean_vm::{F, POSEIDON_16_COL_INDEX_INPUT_START, PrecompileTrace, WitnessPoseidon24};
use multilinear_toolkit::prelude::*;
use p3_koala_bear::{KoalaBearInternalLayerParameters, KoalaBearParameters};
use p3_monty_31::InternalLayerBaseParameters;
use poseidon_circuit::{PoseidonGKRLayers, PoseidonWitness, generate_poseidon_witness};
use tracing::instrument;
use utils::transposed_par_iter_mut;

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
pub fn generate_poseidon_witness_24<const N_COMMITED_CUBES: usize>(
    layers: &PoseidonGKRLayers<24, N_COMMITED_CUBES>,
    inputs: &[WitnessPoseidon24],
) -> PoseidonWitness<FPacking<F>, 24, N_COMMITED_CUBES> {
    let n_poseidons = inputs.len();
    assert!(n_poseidons.is_power_of_two());
    let mut inputs_transposed: [_; 24] =
        array::from_fn(|_| unsafe { uninitialized_vec(n_poseidons) });
    transposed_par_iter_mut(&mut inputs_transposed)
        .enumerate()
        .for_each(|(i, row)| {
            for (j, p) in row.into_iter().enumerate() {
                *p = inputs[i].input[j];
            }
        });
    let inputs_transposed_ref: [_; 24] = array::from_fn(|i| &inputs_transposed[i][..]);
    generate_poseidon_witness_helper::<24, N_COMMITED_CUBES>(layers, &inputs_transposed_ref, None)
}

#[instrument(skip_all)]
pub fn generate_poseidon_witness_16<const N_COMMITED_CUBES: usize>(
    layers: &PoseidonGKRLayers<16, N_COMMITED_CUBES>,
    trace: &PrecompileTrace,
    n_compressions: usize,
) -> PoseidonWitness<FPacking<F>, 16, N_COMMITED_CUBES> {
    let inputs: [_; 16] =
        array::from_fn(|i| &trace.base[POSEIDON_16_COL_INDEX_INPUT_START + i][..]);
    generate_poseidon_witness_helper::<16, N_COMMITED_CUBES>(layers, &inputs, Some(n_compressions))
}

#[instrument(skip_all)]
fn generate_poseidon_witness_helper<const WIDTH: usize, const N_COMMITED_CUBES: usize>(
    layers: &PoseidonGKRLayers<WIDTH, N_COMMITED_CUBES>,
    inputs: &[&[F]; WIDTH],
    n_compressions: Option<usize>,
) -> PoseidonWitness<FPacking<F>, WIDTH, N_COMMITED_CUBES>
where
    KoalaBearInternalLayerParameters: InternalLayerBaseParameters<KoalaBearParameters, WIDTH>,
{
    let n_poseidons = inputs[0].len();
    assert!(n_poseidons.is_power_of_two());
    let inputs_packed: [_; WIDTH] =
        array::from_fn(|i| PFPacking::<F>::pack_slice(&inputs[i]).to_vec()); // TODO avoid cloning
    generate_poseidon_witness::<FPacking<F>, WIDTH, N_COMMITED_CUBES>(
        inputs_packed,
        layers,
        n_compressions.map(|n_compressions| {
            (
                n_compressions,
                PFPacking::<F>::pack_slice(
                    &[
                        vec![F::ZERO; n_poseidons.checked_sub(n_compressions).unwrap()],
                        vec![F::ONE; n_compressions],
                    ]
                    .concat(),
                )
                .to_vec(),
            )
        }),
    )
}
