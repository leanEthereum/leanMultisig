use std::array;
use std::sync::atomic::{AtomicPtr, Ordering};

use backend::*;
use tracing::instrument;

use crate::{F, poseidon_round_constants};

/// Number of GKR layers for Poseidon1-16: 4 initial full + 20 partial + 4 final full + 1 input-with-c0.
pub const POSEIDON_16_N_GKR_LAYERS: usize = 29;

/// Total GKR columns: 29 layers * 16 columns each.
pub const POSEIDON_16_N_GKR_COLS: usize = POSEIDON_16_N_GKR_LAYERS * 16;

/// Fill the poseidon-16 GKR layer columns (and the compressed output columns).
///
/// Arguments:
/// - `trace`: the full table trace (mutable slice of columns).
/// - `input_col_start`: column index where the 16 input columns begin (assumed pre-filled).
/// - `gkr_col_start`: column index where the 29*WIDTH GKR-layer columns begin (filled here).
/// - `compressed_out_col_start`: column index where the 8 compressed output columns begin (filled here).
///   `compressed_out[i] = output_layer[i] + input[i]` for i in 0..8.
#[instrument(skip_all)]
pub fn fill_poseidon_gkr_trace(
    trace: &mut [Vec<F>],
    input_col_start: usize,
    gkr_col_start: usize,
    compressed_out_col_start: usize,
) {
    const WIDTH: usize = 16;
    assert!(trace[0].len().is_power_of_two() && trace[0].len() > packing_width::<F>());
    assert!(trace.iter().all(|col| col.len() == trace[0].len()));

    let (initial_constants, partial_constants, final_constants) = poseidon_round_constants::<WIDTH>();
    let n_initial = initial_constants.len(); // 4
    let n_partial = partial_constants.len(); // 20

    let all_constants: Vec<&[F; WIDTH]> = initial_constants
        .iter()
        .chain(partial_constants.iter())
        .chain(final_constants.iter())
        .collect();
    assert_eq!(all_constants.len(), 28);
    assert_eq!(1 + 28, POSEIDON_16_N_GKR_LAYERS);

    let mut col = gkr_col_start;
    let mut prev_in = input_col_start;

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

        if prev_in < col {
            let (left, right) = trace.split_at_mut(col);
            if is_full_round {
                apply_full_round::<WIDTH>(&left[prev_in..prev_in + WIDTH], &mut right[..WIDTH], next_constants);
            } else {
                apply_partial_round::<WIDTH>(&left[prev_in..prev_in + WIDTH], &mut right[..WIDTH], next_constants);
            }
        } else {
            // prev_in > col case can't happen with our layout
            unreachable!()
        }
        prev_in = col;
        col += WIDTH;
    }

    assert_eq!(col, gkr_col_start + POSEIDON_16_N_GKR_COLS);

    // Compressed outputs: output_layer[i] + input[i] for i in 0..8
    // output_layer (last GKR layer) is at prev_in..prev_in+WIDTH
    fill_compressed_outputs::<WIDTH>(trace, prev_in, input_col_start, compressed_out_col_start);
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

/// Compressed outputs: out[i] = output_layer[i] + input[i] for i in 0..8.
fn fill_compressed_outputs<const WIDTH: usize>(
    trace: &mut [Vec<F>],
    output_layer_start: usize,
    input_col_start: usize,
    out_col_start: usize,
) {
    let n = trace[0].len();
    // Make sure target columns are sized
    for i in 0..(WIDTH / 2) {
        if trace[out_col_start + i].len() != n {
            trace[out_col_start + i].resize(n, F::ZERO);
        }
    }
    for i in 0..(WIDTH / 2) {
        let out_idx = out_col_start + i;
        let layer_idx = output_layer_start + i;
        let in_idx = input_col_start + i;
        if out_idx == layer_idx || out_idx == in_idx {
            panic!("compressed-output column collides with layer/input column");
        }
        // Borrow output, layer, input non-overlappingly
        let (a, b, c) = pick_three_mut(trace, out_idx, layer_idx, in_idx);
        for ((d, l), inp) in FPacking::<F>::pack_slice_mut(&mut a[..n])
            .iter_mut()
            .zip(FPacking::<F>::pack_slice(&b[..n]))
            .zip(FPacking::<F>::pack_slice(&c[..n]))
        {
            *d = *l + *inp;
        }
    }
}

#[inline]
fn pick_three_mut<T>(v: &mut [Vec<T>], i0: usize, i1: usize, i2: usize) -> (&mut Vec<T>, &Vec<T>, &Vec<T>) {
    assert!(i0 != i1 && i0 != i2 && i1 != i2);
    let len = v.len();
    assert!(i0 < len && i1 < len && i2 < len);
    let ptr = v.as_mut_ptr();
    unsafe {
        let a = &mut *ptr.add(i0);
        let b = &*ptr.add(i1);
        let c = &*ptr.add(i2);
        (a, b, c)
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
        mds_circ_16(buff16);
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
        mds_circ_16(buff16);
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
