use tracing::instrument;

use crate::{
    F, POSEIDON_16_NULL_HASH_PTR, PoseidonMode, ZERO_VEC_PTR, poseidon16_precompile_data,
    tables::{Poseidon2Cols, WIDTH, num_cols_poseidon_16, poseidon_16::POSEIDON_16_COL_PRECOMPILE_DATA},
};
use backend::*;

#[instrument(name = "generate Poseidon2 trace", skip_all)]
pub fn fill_trace_poseidon_16(trace: &mut [Vec<F>]) {
    let n = trace.iter().map(|col| col.len()).max().unwrap();
    for col in trace.iter_mut() {
        if col.len() != n {
            col.resize(n, F::ZERO);
        }
    }

    let m = n - (n % packing_width::<F>());
    let trace_packed: Vec<_> = trace[..num_cols_poseidon_16()]
        .iter()
        .map(|col| FPacking::<F>::pack_slice(&col[..m]))
        .collect();

    // fill the packed rows
    (0..n / packing_width::<F>()).into_par_iter().for_each(|i| {
        let ptrs: Vec<*mut FPacking<F>> = trace_packed
            .iter()
            .map(|col| unsafe { (col.as_ptr() as *mut FPacking<F>).add(i) })
            .collect();
        let perm: &mut Poseidon2Cols<&mut FPacking<F>> =
            unsafe { &mut *(ptrs.as_ptr() as *mut Poseidon2Cols<&mut FPacking<F>>) };

        generate_trace_rows_for_perm(perm);
    });

    // fill the remaining rows (non packed)
    for i in m..n {
        let ptrs: Vec<*mut F> = trace[..num_cols_poseidon_16()]
            .iter()
            .map(|col| unsafe { (col.as_ptr() as *mut F).add(i) })
            .collect();
        let perm: &mut Poseidon2Cols<&mut F> = unsafe { &mut *(ptrs.as_ptr() as *mut Poseidon2Cols<&mut F>) };
        generate_trace_rows_for_perm(perm);
    }
}

pub fn default_poseidon_row() -> Vec<F> {
    let n_cols_total = num_cols_poseidon_16() + 1; // +1 for non-AIR precompile_data
    let mut row = vec![F::ZERO; n_cols_total];
    let ptrs: [*mut F; num_cols_poseidon_16()] = std::array::from_fn(|i| unsafe { row.as_mut_ptr().add(i) });

    let perm: &mut Poseidon2Cols<&mut F> = unsafe { &mut *(ptrs.as_ptr() as *mut Poseidon2Cols<&mut F>) };
    perm.inputs.iter_mut().for_each(|x| **x = F::ZERO);
    *perm.flag = F::ZERO;
    *perm.is_compression = F::ONE; // compression mode for padding
    *perm.index_a = F::from_usize(ZERO_VEC_PTR);
    *perm.index_b = F::from_usize(ZERO_VEC_PTR);
    *perm.index_res = F::from_usize(POSEIDON_16_NULL_HASH_PTR);
    *perm.index_res_high = F::from_usize(POSEIDON_16_NULL_HASH_PTR); // same as index_res in compression

    generate_trace_rows_for_perm(perm);

    // Non-AIR precompile_data column
    row[POSEIDON_16_COL_PRECOMPILE_DATA] = poseidon16_precompile_data(PoseidonMode::default());
    row
}

fn generate_trace_rows_for_perm<F: Algebra<KoalaBear> + Copy>(perm: &mut Poseidon2Cols<&mut F>) {
    let inputs: [F; WIDTH] = std::array::from_fn(|i| *perm.inputs[i]);
    let is_compression = *perm.is_compression;
    let mut state = inputs;

    GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(&mut state);

    for (full_round, constants) in perm
        .beginning_full_rounds
        .iter_mut()
        .zip(KOALABEAR_RC16_EXTERNAL_INITIAL.chunks_exact(2))
    {
        generate_2_full_round(&mut state, full_round, &constants[0], &constants[1]);
    }

    for (partial_round, constant) in perm.partial_rounds.iter_mut().zip(&KOALABEAR_RC16_INTERNAL) {
        generate_partial_round(&mut state, partial_round, *constant);
    }

    let n_ending_full_rounds = perm.ending_full_rounds.len();
    for (full_round, constants) in perm
        .ending_full_rounds
        .iter_mut()
        .zip(KOALABEAR_RC16_EXTERNAL_FINAL.chunks_exact(2))
    {
        generate_2_full_round(&mut state, full_round, &constants[0], &constants[1]);
    }

    // Last 2 full rounds
    generate_last_2_full_rounds(
        &mut state,
        &inputs,
        is_compression,
        &mut perm.outputs,
        &mut perm.outputs_high,
        &KOALABEAR_RC16_EXTERNAL_FINAL[2 * n_ending_full_rounds],
        &KOALABEAR_RC16_EXTERNAL_FINAL[2 * n_ending_full_rounds + 1],
    );
}

#[inline]
fn generate_2_full_round<F: Algebra<KoalaBear> + Copy>(
    state: &mut [F; WIDTH],
    post_full_round: &mut [&mut F; WIDTH],
    round_constants_1: &[KoalaBear; WIDTH],
    round_constants_2: &[KoalaBear; WIDTH],
) {
    // Combine addition of round constants and S-box application in a single loop
    for (state_i, const_i) in state.iter_mut().zip(round_constants_1) {
        *state_i += *const_i;
        *state_i = state_i.cube();
    }
    GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(state);

    for (state_i, const_i) in state.iter_mut().zip(round_constants_2.iter()) {
        *state_i += *const_i;
        *state_i = state_i.cube();
    }
    GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(state);

    post_full_round.iter_mut().zip(*state).for_each(|(post, x)| {
        **post = x;
    });
}

#[inline]
fn generate_last_2_full_rounds<F: Algebra<KoalaBear> + Copy>(
    state: &mut [F; WIDTH],
    inputs: &[F; WIDTH],
    is_compression: F,
    outputs: &mut [&mut F; WIDTH / 2],
    outputs_high: &mut [&mut F; WIDTH / 2],
    round_constants_1: &[KoalaBear; WIDTH],
    round_constants_2: &[KoalaBear; WIDTH],
) {
    for (state_i, const_i) in state.iter_mut().zip(round_constants_1) {
        *state_i += *const_i;
        *state_i = state_i.cube();
    }
    GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(state);

    for (state_i, const_i) in state.iter_mut().zip(round_constants_2.iter()) {
        *state_i += *const_i;
        *state_i = state_i.cube();
    }
    GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(state);

    // outputs[i] = state[i] + is_compression * inputs[i]
    for i in 0..WIDTH / 2 {
        *outputs[i] = state[i] + is_compression * inputs[i];
    }
    // outputs_high[i] = state[i+8] + is_compression * (outputs[i] - state[i+8])
    for i in 0..WIDTH / 2 {
        *outputs_high[i] = state[i + WIDTH / 2] + is_compression * (*outputs[i] - state[i + WIDTH / 2]);
    }
}

#[inline]
fn generate_partial_round<F: Algebra<KoalaBear> + Copy>(
    state: &mut [F; WIDTH],
    post_partial_round: &mut F,
    round_constant: KoalaBear,
) {
    state[0] += round_constant;
    state[0] = state[0].cube();
    *post_partial_round = state[0];
    GenericPoseidon2LinearLayersKoalaBear::internal_linear_layer(state);
}
