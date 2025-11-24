use std::array;

use lean_vm::{F, TableTrace};
use multilinear_toolkit::prelude::*;
use p3_koala_bear::{KoalaBearInternalLayerParameters, KoalaBearParameters};
use p3_monty_31::InternalLayerBaseParameters;
use poseidon_circuit::{PoseidonGKRLayers, PoseidonWitness, generate_poseidon_witness};
use tracing::instrument;

#[instrument(skip_all)]
pub fn generate_poseidon_witness_helper<const WIDTH: usize, const N_COMMITED_CUBES: usize>(
    layers: &PoseidonGKRLayers<WIDTH, N_COMMITED_CUBES>,
    trace: &TableTrace,
    start_index: usize,
    compressions: Option<&[F]>,
) -> PoseidonWitness<FPacking<F>, WIDTH, N_COMMITED_CUBES>
where
    KoalaBearInternalLayerParameters: InternalLayerBaseParameters<KoalaBearParameters, WIDTH>,
{
    let inputs: [_; WIDTH] = array::from_fn(|i| &trace.base[start_index + i][..]);
    let n_poseidons = inputs[0].len();
    assert!(n_poseidons.is_power_of_two());
    let inputs_packed: [_; WIDTH] =
        array::from_fn(|i| PFPacking::<F>::pack_slice(inputs[i]).to_vec()); // TODO avoid cloning
    generate_poseidon_witness::<FPacking<F>, WIDTH, N_COMMITED_CUBES>(
        inputs_packed,
        layers,
        compressions.map(|c| FPacking::<F>::pack_slice(c).to_vec()), // TODO avoid cloning
    )
}
