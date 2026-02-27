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

    let (initial_constants, internal_constants, final_constants) = poseidon_round_constants::<WIDTH>();
    let n_gkr_layers = initial_constants.len() + internal_constants.len() + final_constants.len() + 1;
    assert_eq!(n_gkr_layers, POSEIDON_16_N_GKR_LAYERS);

    let mut col = POSEIDON_16_GKR_START;
    let mut prev_in = 4; // input columns start at index 4

    for (i, constants) in initial_constants
        .iter()
        .map(Some)
        .chain(std::iter::once(None))
        .enumerate()
    {
        let (left, right) = trace.split_at_mut(col);
        apply_full_round::<WIDTH>(&left[prev_in..], &mut right[..WIDTH], constants, i > 0);
        prev_in = col;
        col += WIDTH;
    }
    add_constant_to_col(&mut trace[prev_in], internal_constants[0]);

    for constant in internal_constants[1..]
        .iter()
        .copied()
        .chain(std::iter::once(final_constants[0][0]))
    {
        let (left, right) = trace.split_at_mut(col);
        apply_partial_round::<WIDTH>(&left[prev_in..], &mut right[..WIDTH], constant);
        prev_in = col;
        col += WIDTH;
    }
    for j in 1..WIDTH {
        add_constant_to_col(&mut trace[prev_in + j], final_constants[0][j]);
    }

    for constants in final_constants[1..].iter().map(Some).chain(std::iter::once(None)) {
        let (left, right) = trace.split_at_mut(col);
        apply_full_round::<WIDTH>(&left[prev_in..], &mut right[..WIDTH], constants, true);
        prev_in = col;
        col += WIDTH;
    }

    assert_eq!(col, POSEIDON_16_GKR_START + POSEIDON_16_N_GKR_COLS);

    // Compressed outputs: output_layer[i] + input[i] for i in 0..8
    let output_col_start = col;
    let output_layer_start = col - WIDTH;
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

fn add_constant_to_col(col: &mut [F], constant: F) {
    let c = FPacking::<F>::from(constant);
    for val in FPacking::<F>::pack_slice_mut(col) {
        *val += c;
    }
}

fn apply_full_round<const WIDTH: usize>(
    input_cols: &[Vec<F>],
    output_cols: &mut [Vec<F>],
    constants: Option<&[F; WIDTH]>,
    cube: bool,
) where
    KoalaBearInternalLayerParameters: InternalLayerBaseParameters<KoalaBearParameters, WIDTH>,
{
    let packed_inputs: [&[FPacking<F>]; WIDTH] = array::from_fn(|i| FPacking::<F>::pack_slice(&input_cols[i]));
    let n_packed = packed_inputs[0].len();

    let mut iter = output_cols.iter_mut();
    let out_ptrs: [AtomicPtr<FPacking<F>>; WIDTH] =
        array::from_fn(|_| AtomicPtr::new(FPacking::<F>::pack_slice_mut(iter.next().unwrap()).as_mut_ptr()));

    (0..n_packed).into_par_iter().for_each(|row| {
        let mut buff: [FPacking<F>; WIDTH] = array::from_fn(|j| packed_inputs[j][row]);
        if cube {
            for v in &mut buff {
                *v = v.cube();
            }
        }
        GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(&mut buff);
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

fn apply_partial_round<const WIDTH: usize>(input_cols: &[Vec<F>], output_cols: &mut [Vec<F>], constant: F)
where
    KoalaBearInternalLayerParameters: InternalLayerBaseParameters<KoalaBearParameters, WIDTH>,
{
    let packed_inputs: [&[FPacking<F>]; WIDTH] = array::from_fn(|i| FPacking::<F>::pack_slice(&input_cols[i]));
    let n_packed = packed_inputs[0].len();

    let mut iter = output_cols.iter_mut();
    // SAFETY: same as apply_full_round — distinct columns, non-aliasing row indices.
    let out_ptrs: [AtomicPtr<FPacking<F>>; WIDTH] =
        array::from_fn(|_| AtomicPtr::new(FPacking::<F>::pack_slice_mut(iter.next().unwrap()).as_mut_ptr()));

    (0..n_packed).into_par_iter().for_each(|row| {
        let mut buff = [FPacking::<F>::ZERO; WIDTH];
        buff[0] = packed_inputs[0][row].cube();
        for j in 1..WIDTH {
            buff[j] = packed_inputs[j][row];
        }
        GenericPoseidon2LinearLayersKoalaBear::internal_linear_layer(&mut buff);
        buff[0] += constant;
        for j in 0..WIDTH {
            unsafe { *out_ptrs[j].load(Ordering::Relaxed).add(row) = buff[j] };
        }
    });
}
