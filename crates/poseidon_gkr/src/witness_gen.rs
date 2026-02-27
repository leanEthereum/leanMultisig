use std::array;
use std::sync::atomic::{AtomicPtr, Ordering};

use backend::*;
use tracing::instrument;

use crate::{F, poseidon_round_constants};

/// Start of GKR layer columns in the poseidon-16 trace.
pub const POSEIDON_16_GKR_START: usize = 20;

/// Number of GKR layers: 4 initial full + 20 partial + 4 final full + 1 output.
pub const POSEIDON_16_N_GKR_LAYERS: usize = 29;

/// Total GKR columns: 29 layers * 16 columns each.
pub const POSEIDON_16_N_GKR_COLS: usize = POSEIDON_16_N_GKR_LAYERS * 16;

/// Total columns in the poseidon-16 trace: 20 (metadata+inputs) + 464 (GKR) + 8 (compressed outputs).
pub const POSEIDON_16_N_TOTAL_COLS: usize = POSEIDON_16_GKR_START + POSEIDON_16_N_GKR_COLS + 8;

/// Fill the poseidon-16 trace columns [20..492] from the input columns [4..20].
/// The first 20 columns (flag, addresses, inputs) must already be filled.
#[instrument(skip_all)]
pub fn fill_poseidon_trace(trace: &mut [Vec<F>]) {
    const WIDTH: usize = 16;
    assert_eq!(trace.len(), POSEIDON_16_N_TOTAL_COLS);
    assert!(trace[0].len().is_power_of_two() && trace[0].len() > packing_width::<F>());
    assert!(trace.iter().all(|col| col.len() == trace[0].len()));

    let (initial_constants, partial_constants, final_constants) = poseidon_round_constants::<WIDTH>();
    let n_initial = initial_constants.len(); // 4
    let n_partial = partial_constants.len(); // 20

    // Concatenate all 28 rounds of constants for easier indexing
    let all_constants: Vec<&[F; WIDTH]> = initial_constants
        .iter()
        .chain(partial_constants.iter())
        .chain(final_constants.iter())
        .collect();
    assert_eq!(all_constants.len(), 28);
    assert_eq!(1 + 28, POSEIDON_16_N_GKR_LAYERS);

    let mut col = POSEIDON_16_GKR_START;
    let mut prev_in = 4; // input columns start at index 4

    // Layer 0: input + constants[0] (Poseidon1 has no initial linear layer)
    add_constants_to_cols::<WIDTH>(trace, prev_in, col, all_constants[0]);
    prev_in = col;
    col += WIDTH;

    // Layers 1..28: each computed from the previous using round k's S-box type
    for round in 0..28 {
        let next_constants: Option<&[F; WIDTH]> = if round < 27 {
            Some(all_constants[round + 1])
        } else {
            None
        };
        let is_full_round = round < n_initial || round >= n_initial + n_partial;

        let (left, right) = trace.split_at_mut(col);
        if is_full_round {
            apply_full_round::<WIDTH>(&left[prev_in..], &mut right[..WIDTH], next_constants);
        } else {
            apply_partial_round::<WIDTH>(&left[prev_in..], &mut right[..WIDTH], next_constants);
        }
        prev_in = col;
        col += WIDTH;
    }

    assert_eq!(col, POSEIDON_16_GKR_START + POSEIDON_16_N_GKR_COLS);

    // Compressed outputs: output_layer[i] + input[i] for i in 0..8
    let output_col_start = col;
    let output_layer_start = prev_in;
    for i in 0..8 {
        let (before, after) = trace.split_at_mut(output_col_start + i);
        let dst = &mut after[0];
        for (d, (&a, &b)) in dst
            .iter_mut()
            .zip(before[output_layer_start + i].iter().zip(before[4 + i].iter()))
        {
            *d = a + b;
        }
    }
}

/// Layer 0 helper: output[j] = input[j] + constants[j] for all j.
fn add_constants_to_cols<const WIDTH: usize>(
    trace: &mut [Vec<F>],
    input_start: usize,
    output_start: usize,
    constants: &[F; WIDTH],
) {
    let n = trace[0].len();
    for j in 0..WIDTH {
        let c = FPacking::<F>::from(constants[j]);
        trace[output_start + j] = trace[input_start + j].clone();
        for val in FPacking::<F>::pack_slice_mut(&mut trace[output_start + j][..n]) {
            *val += c;
        }
    }
}

/// Full round: cube all → circulant MDS → optionally add constants.
fn apply_full_round<const WIDTH: usize>(
    input_cols: &[Vec<F>],
    output_cols: &mut [Vec<F>],
    constants: Option<&[F; WIDTH]>,
) {
    assert_eq!(WIDTH, 16);
    let packed_inputs: [&[FPacking<F>]; WIDTH] = array::from_fn(|i| FPacking::<F>::pack_slice(&input_cols[i]));
    let n_packed = packed_inputs[0].len();

    let mut iter = output_cols.iter_mut();
    let out_ptrs: [AtomicPtr<FPacking<F>>; WIDTH] =
        array::from_fn(|_| AtomicPtr::new(FPacking::<F>::pack_slice_mut(iter.next().unwrap()).as_mut_ptr()));

    (0..n_packed).into_par_iter().for_each(|row| {
        let mut buff: [FPacking<F>; WIDTH] = array::from_fn(|j| packed_inputs[j][row]);
        for v in &mut buff {
            *v = v.cube();
        }
        let buff16: &mut [FPacking<F>; 16] = (&mut buff[..]).try_into().unwrap();
        mds_circulant_16_karatsuba(buff16);
        if let Some(constants) = constants {
            for j in 0..WIDTH {
                buff[j] += constants[j];
            }
        }
        for j in 0..WIDTH {
            unsafe { *out_ptrs[j].load(Ordering::Relaxed).add(row) = buff[j] };
        }
    });
}

/// Partial round: cube state[0] only → circulant MDS → optionally add constants.
fn apply_partial_round<const WIDTH: usize>(
    input_cols: &[Vec<F>],
    output_cols: &mut [Vec<F>],
    constants: Option<&[F; WIDTH]>,
) {
    assert_eq!(WIDTH, 16);
    let packed_inputs: [&[FPacking<F>]; WIDTH] = array::from_fn(|i| FPacking::<F>::pack_slice(&input_cols[i]));
    let n_packed = packed_inputs[0].len();

    let mut iter = output_cols.iter_mut();
    let out_ptrs: [AtomicPtr<FPacking<F>>; WIDTH] =
        array::from_fn(|_| AtomicPtr::new(FPacking::<F>::pack_slice_mut(iter.next().unwrap()).as_mut_ptr()));

    (0..n_packed).into_par_iter().for_each(|row| {
        let mut buff: [FPacking<F>; WIDTH] = array::from_fn(|j| packed_inputs[j][row]);
        buff[0] = buff[0].cube();
        let buff16: &mut [FPacking<F>; 16] = (&mut buff[..]).try_into().unwrap();
        mds_circulant_16_karatsuba(buff16);
        if let Some(constants) = constants {
            for j in 0..WIDTH {
                buff[j] += constants[j];
            }
        }
        for j in 0..WIDTH {
            unsafe { *out_ptrs[j].load(Ordering::Relaxed).add(row) = buff[j] };
        }
    });
}
