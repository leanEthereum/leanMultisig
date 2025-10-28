use std::array;

use multilinear_toolkit::prelude::*;
use p3_koala_bear::GenericPoseidon2LinearLayersKoalaBear;
use p3_koala_bear::KoalaBearInternalLayerParameters;
use p3_koala_bear::KoalaBearParameters;
use p3_monty_31::InternalLayerBaseParameters;
use p3_poseidon2::GenericPoseidon2LinearLayers;
use utils::transposed_par_iter_mut;

use crate::F;

pub fn apply_mds_matrix<A, const WIDTH: usize>(input_layers: &[Vec<A>; WIDTH]) -> [Vec<A>; WIDTH]
where
    A: Algebra<F> + Copy + Send + Sync,
    KoalaBearInternalLayerParameters: InternalLayerBaseParameters<KoalaBearParameters, WIDTH>,
{
    // MDS permutation
    let mut output_layers: [_; WIDTH] = array::from_fn(|_| A::zero_vec(input_layers[0].len()));
    transposed_par_iter_mut(&mut output_layers)
        .enumerate()
        .for_each(|(row_index, output_row)| {
            let mut buff: [A; WIDTH] = array::from_fn(|j| input_layers[j][row_index]);
            GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(&mut buff);
            for j in 0..WIDTH {
                *output_row[j] = buff[j];
            }
        });
    output_layers
}

pub fn apply_light_matrix<A, const WIDTH: usize>(input_layers: &[Vec<A>; WIDTH]) -> [Vec<A>; WIDTH]
where
    A: Algebra<F> + Copy + Send + Sync,
    KoalaBearInternalLayerParameters: InternalLayerBaseParameters<KoalaBearParameters, WIDTH>,
{
    let mut output_layers: [_; WIDTH] = array::from_fn(|_| A::zero_vec(input_layers[0].len()));
    transposed_par_iter_mut(&mut output_layers)
        .enumerate()
        .for_each(|(row_index, output_row)| {
            let mut buff: [A; WIDTH] = array::from_fn(|j| input_layers[j][row_index]);
            GenericPoseidon2LinearLayersKoalaBear::internal_linear_layer(&mut buff);
            for j in 0..WIDTH {
                *output_row[j] = buff[j];
            }
        });
    output_layers
}

pub fn apply_cubes<A, const WIDTH: usize>(
    input_layers: &[Vec<A>; WIDTH],
    constants: &[F; WIDTH],
) -> [Vec<A>; WIDTH]
where
    A: Algebra<F> + Copy + Send + Sync,
{
    array::from_fn(|j| cube(&input_layers[j], constants[j]))
}

pub fn cube<A>(input_layers: &Vec<A>, constant: F) -> Vec<A>
where
    A: Algebra<F> + Copy + Send + Sync,
{
    input_layers
        .par_iter()
        .map(|&x| (x + constant).cube())
        .collect()
}
