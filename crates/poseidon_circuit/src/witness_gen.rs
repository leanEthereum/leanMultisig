use std::array;

use multilinear_toolkit::prelude::*;
use p3_koala_bear::GenericPoseidon2LinearLayersKoalaBear;
use p3_koala_bear::KoalaBearInternalLayerParameters;
use p3_koala_bear::KoalaBearParameters;
use p3_monty_31::InternalLayerBaseParameters;
use p3_poseidon2::GenericPoseidon2LinearLayers;
use utils::transposed_par_iter_mut;

use crate::gkr_layers::BatchPartialRounds;
use crate::gkr_layers::PartialRoundComputation;
use crate::gkr_layers::PoseidonGKRLayers;
use crate::{F, gkr_layers::FullRoundComputation};

#[derive(Debug)]
pub struct PoseidonWitness<A, const WIDTH: usize, const N_COMMITED_CUBES: usize> {
    pub input_layer: [Vec<A>; WIDTH], // input of the permutation
    pub remaining_initial_full_round_inputs: Vec<[Vec<A>; WIDTH]>, // the remaining input of each initial full round
    pub batch_partial_round_input: [Vec<A>; WIDTH], // again, the input of the batch (partial) round
    pub committed_cubes: [Vec<A>; N_COMMITED_CUBES], // the cubes commited in the batch (partial) rounds
    pub remaining_partial_round_inputs: Vec<[Vec<A>; WIDTH]>, // the input of each remaining partial round
    pub final_full_round_inputs: Vec<[Vec<A>; WIDTH]>,        // the input of each final full round
    pub output_layer: [Vec<A>; WIDTH],                        // output of the permutation
    pub compression: Option<(usize, Vec<A>)>, // num compressions, compression indicator column
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
    let mut remaining_initial_full_layers = vec![apply_full_round::<_, _, true>(
        &input,
        &layers.initial_full_round,
        None,
    )];
    for round in &layers.initial_full_rounds_remaining {
        remaining_initial_full_layers.push(apply_full_round::<_, _, false>(
            remaining_initial_full_layers.last().unwrap(),
            round,
            None,
        ));
    }

    let batch_partial_round_layer = remaining_initial_full_layers.pop().unwrap();
    let (next_layer, committed_cubes) =
        apply_batch_partial_rounds(&batch_partial_round_layer, &layers.batch_partial_rounds);

    let mut remaining_partial_inputs = vec![next_layer];
    for constant in &layers.partial_rounds_remaining {
        remaining_partial_inputs.push(apply_partial_round(
            remaining_partial_inputs.last().unwrap(),
            constant,
        ));
    }

    let mut final_full_layer_inputs = vec![remaining_partial_inputs.pop().unwrap()];
    for (i, round) in layers.final_full_rounds.iter().enumerate() {
        final_full_layer_inputs.push(apply_full_round::<_, _, false>(
            final_full_layer_inputs.last().unwrap(),
            round,
            if i == layers.final_full_rounds.len() - 1 {
                compression.as_ref().map(|(_, v)| v.as_slice())
            } else {
                None
            },
        ));
    }

    let output_layer = final_full_layer_inputs.pop().unwrap();

    PoseidonWitness {
        input_layer: input,
        remaining_initial_full_round_inputs: remaining_initial_full_layers,
        batch_partial_round_input: batch_partial_round_layer,
        committed_cubes,
        remaining_partial_round_inputs: remaining_partial_inputs,
        final_full_round_inputs: final_full_layer_inputs,
        output_layer,
        compression,
    }
}

// #[instrument(skip_all)]
fn apply_full_round<A, const WIDTH: usize, const FIRST: bool>(
    input_layers: &[Vec<A>; WIDTH],
    full_round: &FullRoundComputation<WIDTH, FIRST>,
    compression_indicator: Option<&[A]>,
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
            if FIRST {
                GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(&mut buff);
            }
            buff.iter_mut().enumerate().for_each(|(j, val)| {
                *val = (*val + full_round.constants[j]).cube();
            });
            GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(&mut buff);
            if let Some(compression_output_width) = full_round.compressed_output {
                let compressed = compression_indicator.unwrap()[row_index];
                for i in 0..compression_output_width {
                    *output_row[i] = buff[i];
                }
                for i in compression_output_width..WIDTH {
                    *output_row[i] = buff[i] * (A::ONE - compressed);
                }
            } else {
                for j in 0..WIDTH {
                    *output_row[j] = buff[j];
                }
            }
        });
    output_layers
}

// #[instrument(skip_all)]
fn apply_partial_round<A, const WIDTH: usize>(
    input_layers: &[Vec<A>],
    partial_round: &PartialRoundComputation<WIDTH>,
) -> [Vec<A>; WIDTH]
where
    A: Algebra<F> + Copy + Send + Sync,
    KoalaBearInternalLayerParameters: InternalLayerBaseParameters<KoalaBearParameters, WIDTH>,
{
    let mut output_layers: [_; WIDTH] = array::from_fn(|_| A::zero_vec(input_layers[0].len()));
    transposed_par_iter_mut(&mut output_layers)
        .enumerate()
        .for_each(|(row_index, output_row)| {
            let first_cubed = (input_layers[0][row_index] + partial_round.constant).cube();
            let mut buff = [A::ZERO; WIDTH];
            buff[0] = first_cubed;
            for j in 1..WIDTH {
                buff[j] = input_layers[j][row_index];
            }
            GenericPoseidon2LinearLayersKoalaBear::internal_linear_layer(&mut buff);
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
        if layers
            .final_full_rounds
            .last()
            .unwrap()
            .compressed_output
            .is_some()
        {
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
