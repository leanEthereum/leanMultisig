use std::array;

use multilinear_toolkit::prelude::*;
use p3_koala_bear::GenericPoseidon2LinearLayersKoalaBear;
use p3_koala_bear::KoalaBearInternalLayerParameters;
use p3_koala_bear::KoalaBearParameters;
use p3_monty_31::InternalLayerBaseParameters;
use p3_poseidon2::GenericPoseidon2LinearLayers;
use utils::transposed_par_iter_mut;

use crate::F;
use crate::gkr_layers::BatchPartialRounds;
use crate::gkr_layers::PoseidonGKRLayers;

#[derive(Debug)]
pub struct PoseidonWitness<A, const WIDTH: usize, const N_COMMITED_CUBES: usize> {
    pub input_layer: [Vec<A>; WIDTH], // input of the permutation
    pub initial_full_layers: Vec<[Vec<A>; WIDTH]>, // just before cubing
    pub batch_partial_round_input: [Vec<A>; WIDTH], // again, the input of the batch (partial) round
    pub committed_cubes: [Vec<A>; N_COMMITED_CUBES], // the cubes commited in the batch (partial) rounds
    pub remaining_partial_round_layers: Vec<[Vec<A>; WIDTH]>, // the input of each remaining partial round, just before cubing the first element
    pub final_full_layers: Vec<[Vec<A>; WIDTH]>,              // just before cubing
    pub output_layer: [Vec<A>; WIDTH],                        // output of the permutation
    pub compression: Option<(usize, Vec<A>, [Vec<A>; WIDTH])>, // num compressions, compression indicator column, compressed output
}

impl<const WIDTH: usize, const N_COMMITED_CUBES: usize>
    PoseidonWitness<FPacking<F>, WIDTH, N_COMMITED_CUBES>
{
    pub fn n_poseidons(&self) -> usize {
        self.input_layer[0].len() * packing_width::<F>()
    }
}

pub fn generate_poseidon_witness<A, const WIDTH: usize, const N_COMMITED_CUBES: usize>(
    input: [Vec<A>; WIDTH],
    layers: &PoseidonGKRLayers<WIDTH, N_COMMITED_CUBES>,
    compression: Option<(usize, Vec<A>)>,
) -> PoseidonWitness<A, WIDTH, N_COMMITED_CUBES>
where
    A: Algebra<F> + Copy + Send + Sync,
    KoalaBearInternalLayerParameters: InternalLayerBaseParameters<KoalaBearParameters, WIDTH>,
{
    let mut initial_full_layers = vec![apply_full_round::<_, _, false, true, true>(
        &input,
        &layers.initial_full_rounds[0],
    )];
    for constants in &layers.initial_full_rounds[1..] {
        initial_full_layers.push(apply_full_round::<_, _, true, true, true>(
            initial_full_layers.last().unwrap(),
            constants,
        ));
    }

    let batch_partial_round_layer = apply_full_round::<_, _, true, true, false>(
        initial_full_layers.last().unwrap(),
        &[F::ZERO; WIDTH], // unused
    );
    let (mut next_layer, committed_cubes) =
        apply_batch_partial_rounds(&batch_partial_round_layer, &layers.batch_partial_rounds);

    next_layer[0] = next_layer[0]
        .par_iter()
        .map(|&val| val + layers.partial_rounds_remaining[0])
        .collect();
    let mut remaining_partial_round_layers = vec![next_layer];
    for &constant in &layers.partial_rounds_remaining[1..] {
        remaining_partial_round_layers.push(apply_partial_round(
            remaining_partial_round_layers.last().unwrap(),
            Some(constant),
        ));
    }

    let mut final_full_layers = vec![apply_full_round::<_, _, false, false, true>(
        &apply_partial_round(remaining_partial_round_layers.last().unwrap(), None),
        &layers.final_full_rounds[0],
    )];
    for constants in &layers.final_full_rounds[1..] {
        final_full_layers.push(apply_full_round::<_, _, true, true, true>(
            final_full_layers.last().unwrap(),
            constants,
        ));
    }

    let output_layer = apply_full_round::<_, _, true, true, false>(
        final_full_layers.last().unwrap(),
        &[F::ZERO; WIDTH], // unused
    );

    let compression = compression.map(|(n_compressions, indicator)| {
        let compressed_output = (0..WIDTH)
            .into_par_iter()
            .map(|col_idx| {
                if col_idx < layers.compressed_output.unwrap() {
                    output_layer[col_idx].clone()
                } else {
                    output_layer[col_idx]
                        .iter()
                        .zip(&indicator)
                        .map(|(out, ind)| *out * (A::ONE - *ind))
                        .collect::<Vec<_>>()
                }
            })
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();
        (n_compressions, indicator, compressed_output)
    });

    PoseidonWitness {
        input_layer: input,
        initial_full_layers,
        batch_partial_round_input: batch_partial_round_layer,
        committed_cubes,
        remaining_partial_round_layers,
        final_full_layers,
        output_layer,
        compression,
    }
}

// #[instrument(skip_all)]
fn apply_full_round<
    A,
    const WIDTH: usize,
    const CUBE: bool,
    const MDS: bool,
    const ADD_CONSTANTS: bool,
>(
    input_layers: &[Vec<A>; WIDTH],
    constants: &[F; WIDTH],
) -> [Vec<A>; WIDTH]
where
    A: Algebra<F> + Copy + Send + Sync,
    KoalaBearInternalLayerParameters: InternalLayerBaseParameters<KoalaBearParameters, WIDTH>,
{
    let mut output_layers: [_; WIDTH] = array::from_fn(|_| A::zero_vec(input_layers[0].len()));
    transposed_par_iter_mut(&mut output_layers)
        .enumerate()
        .for_each(|(row_index, output_row)| {
            let mut buff: [A; WIDTH] = array::from_fn(|j| input_layers[j][row_index]);
            if CUBE {
                for j in 0..WIDTH {
                    buff[j] = buff[j].cube();
                }
            }
            if MDS {
                GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(&mut buff);
            }
            if ADD_CONSTANTS {
                buff.iter_mut().enumerate().for_each(|(j, val)| {
                    *val += constants[j];
                });
            }
            for j in 0..WIDTH {
                *output_row[j] = buff[j];
            }
        });
    output_layers
}

// #[instrument(skip_all)]
fn apply_partial_round<A, const WIDTH: usize>(
    input_layers: &[Vec<A>],
    partial_round_constant: Option<F>,
) -> [Vec<A>; WIDTH]
where
    A: Algebra<F> + Copy + Send + Sync,
    KoalaBearInternalLayerParameters: InternalLayerBaseParameters<KoalaBearParameters, WIDTH>,
{
    // cube single, light matrix mul, add single constant
    let mut output_layers: [_; WIDTH] = array::from_fn(|_| A::zero_vec(input_layers[0].len()));
    transposed_par_iter_mut(&mut output_layers)
        .enumerate()
        .for_each(|(row_index, output_row)| {
            let mut buff = [A::ZERO; WIDTH];
            buff[0] = input_layers[0][row_index].cube();
            for j in 1..WIDTH {
                buff[j] = input_layers[j][row_index];
            }
            GenericPoseidon2LinearLayersKoalaBear::internal_linear_layer(&mut buff);
            if let Some(constant) = partial_round_constant {
                buff[0] += constant;
            }
            for j in 0..WIDTH {
                *output_row[j] = buff[j];
            }
        });
    output_layers
}

// #[instrument(skip_all)]
fn apply_batch_partial_rounds<A, const WIDTH: usize, const N_COMMITED_CUBES: usize>(
    input_layers: &[Vec<A>],
    rounds: &BatchPartialRounds<WIDTH, N_COMMITED_CUBES>,
) -> ([Vec<A>; WIDTH], [Vec<A>; N_COMMITED_CUBES])
where
    A: Algebra<F> + Copy + Send + Sync,
    KoalaBearInternalLayerParameters: InternalLayerBaseParameters<KoalaBearParameters, WIDTH>,
{
    let mut output_layers: [_; WIDTH] = array::from_fn(|_| A::zero_vec(input_layers[0].len()));
    let mut cubes: [_; N_COMMITED_CUBES] = array::from_fn(|_| A::zero_vec(input_layers[0].len()));
    transposed_par_iter_mut(&mut output_layers)
        .zip(transposed_par_iter_mut(&mut cubes))
        .enumerate()
        .for_each(|(row_index, (output_row, cubes))| {
            let mut buff: [A; WIDTH] = array::from_fn(|j| input_layers[j][row_index]);
            for (i, &constant) in rounds.constants.iter().enumerate() {
                *cubes[i] = (buff[0] + constant).cube();
                buff[0] = *cubes[i];
                GenericPoseidon2LinearLayersKoalaBear::internal_linear_layer(&mut buff);
            }
            buff[0] = (buff[0] + rounds.last_constant).cube();
            GenericPoseidon2LinearLayersKoalaBear::internal_linear_layer(&mut buff);
            for j in 0..WIDTH {
                *output_row[j] = buff[j];
            }
        });
    (output_layers, cubes)
}

pub fn default_cube_layers<A, const WIDTH: usize, const N_COMMITED_CUBES: usize>(
    layers: &PoseidonGKRLayers<WIDTH, N_COMMITED_CUBES>,
) -> [A; N_COMMITED_CUBES]
where
    A: Algebra<F> + Copy + Send + Sync,
    KoalaBearInternalLayerParameters: InternalLayerBaseParameters<KoalaBearParameters, WIDTH>,
{
    generate_poseidon_witness::<A, WIDTH, N_COMMITED_CUBES>(
        array::from_fn(|_| vec![A::ZERO]),
        layers,
        if layers.compressed_output.is_some() {
            Some((0, vec![A::ZERO]))
        } else {
            None
        },
    )
    .committed_cubes
    .iter()
    .map(|v| v[0])
    .collect::<Vec<_>>()
    .try_into()
    .unwrap()
}
