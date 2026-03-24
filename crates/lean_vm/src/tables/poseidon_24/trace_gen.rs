use tracing::instrument;

use crate::{
    F, POSEIDON_24_MODE_COMPRESS_0_9, ZERO_VEC_PTR,
    tables::{
        POSEIDON_24_COL_PRECOMPILE_DATA, POSEIDON_24_OUTPUT_SIZE, POSEIDON_24_PRECOMPILE_DATA_OFFSET, Poseidon1Cols24,
        WIDTH_24, num_cols_poseidon_24,
    },
};
use backend::*;

#[instrument(name = "generate Poseidon24 AIR trace", skip_all)]
pub fn fill_trace_poseidon_24(trace: &mut [Vec<F>]) {
    let n = trace.iter().map(|col| col.len()).max().unwrap();
    for col in trace.iter_mut() {
        if col.len() != n {
            col.resize(n, F::ZERO);
        }
    }

    let m = n - (n % packing_width::<F>());
    let trace_packed: Vec<_> = trace.iter().map(|col| FPacking::<F>::pack_slice(&col[..m])).collect();

    // fill the packed rows
    (0..m / packing_width::<F>()).into_par_iter().for_each(|i| {
        let ptrs: Vec<*mut FPacking<F>> = trace_packed
            .iter()
            .map(|col| unsafe { (col.as_ptr() as *mut FPacking<F>).add(i) })
            .collect();
        let perm: &mut Poseidon1Cols24<&mut FPacking<F>> =
            unsafe { &mut *(ptrs.as_ptr() as *mut Poseidon1Cols24<&mut FPacking<F>>) };

        generate_trace_rows_for_perm_24(perm);
    });

    // fill the remaining rows (non packed)
    for i in m..n {
        let ptrs: Vec<*mut F> = trace
            .iter()
            .map(|col| unsafe { (col.as_ptr() as *mut F).add(i) })
            .collect();
        let perm: &mut Poseidon1Cols24<&mut F> = unsafe { &mut *(ptrs.as_ptr() as *mut Poseidon1Cols24<&mut F>) };
        generate_trace_rows_for_perm_24(perm);
    }
}

pub fn default_poseidon_24_row(null_hash_ptr: usize) -> Vec<F> {
    let mut row = vec![F::ZERO; num_cols_poseidon_24() + 1];
    let ptrs: Vec<*mut F> = (0..num_cols_poseidon_24())
        .map(|i| unsafe { row.as_mut_ptr().add(i) })
        .collect();

    let perm: &mut Poseidon1Cols24<&mut F> = unsafe { &mut *(ptrs.as_ptr() as *mut Poseidon1Cols24<&mut F>) };
    perm.inputs.iter_mut().for_each(|x| **x = F::ZERO);
    *perm.flag = F::ZERO;
    *perm.is_compress_0_9 = F::ONE; // convention
    *perm.is_permute_0_9 = F::ZERO;
    *perm.index_input_left = F::from_usize(ZERO_VEC_PTR);
    *perm.index_input_right = F::from_usize(ZERO_VEC_PTR);
    *perm.index_res = F::from_usize(null_hash_ptr);

    generate_trace_rows_for_perm_24(perm);
    // virtual column
    row[POSEIDON_24_COL_PRECOMPILE_DATA] =
        F::from_usize(POSEIDON_24_PRECOMPILE_DATA_OFFSET + POSEIDON_24_MODE_COMPRESS_0_9); // ...following the above convention
    row
}

fn generate_trace_rows_for_perm_24<F: Algebra<KoalaBear> + Copy>(perm: &mut Poseidon1Cols24<&mut F>) {
    let inputs: [F; WIDTH_24] = std::array::from_fn(|i| *perm.inputs[i]);
    let mut state = inputs;

    // No initial linear layer for Poseidon1

    for (full_round, constants) in perm
        .beginning_full_rounds
        .iter_mut()
        .zip(poseidon1_24_initial_constants().chunks_exact(2))
    {
        generate_2_full_round_24(&mut state, full_round, &constants[0], &constants[1]);
    }

    // --- Sparse partial rounds ---
    let frc = poseidon1_24_sparse_first_round_constants();
    for (s, &c) in state.iter_mut().zip(frc.iter()) {
        *s += c;
    }
    let m_i = poseidon1_24_sparse_m_i();
    let input_for_mi = state;
    for i in 0..WIDTH_24 {
        let mut acc = F::ZERO;
        for j in 0..WIDTH_24 {
            acc += input_for_mi[j] * m_i[i][j];
        }
        state[i] = acc;
    }

    let first_rows = poseidon1_24_sparse_first_row();
    let v_vecs = poseidon1_24_sparse_v();
    let scalar_rc = poseidon1_24_sparse_scalar_round_constants();
    let n_partial = perm.partial_rounds.len();
    for round in 0..n_partial {
        // S-box on state[0]
        state[0] = state[0].cube();
        *perm.partial_rounds[round] = state[0];
        // Scalar round constant (not on last round)
        if round < n_partial - 1 {
            state[0] += scalar_rc[round];
        }
        // Sparse matrix
        let old_s0 = state[0];
        let mut new_s0 = F::ZERO;
        for j in 0..WIDTH_24 {
            new_s0 += state[j] * first_rows[round][j];
        }
        state[0] = new_s0;
        for i in 1..WIDTH_24 {
            state[i] += old_s0 * v_vecs[round][i - 1];
        }
    }

    let n_ending_full_rounds = perm.ending_full_rounds.len();
    for (full_round, constants) in perm
        .ending_full_rounds
        .iter_mut()
        .zip(poseidon1_24_final_constants().chunks_exact(2))
    {
        generate_2_full_round_24(&mut state, full_round, &constants[0], &constants[1]);
    }

    // Last 2 full rounds with conditional feedforward and output selection
    let is_compress = *perm.is_compress_0_9;
    let is_output_0_9 = *perm.is_compress_0_9 + *perm.is_permute_0_9;
    generate_last_2_full_rounds_24(
        &mut state,
        &inputs,
        &mut perm.outputs,
        &poseidon1_24_final_constants()[2 * n_ending_full_rounds],
        &poseidon1_24_final_constants()[2 * n_ending_full_rounds + 1],
        is_compress,
        is_output_0_9,
    );
}

#[inline]
fn generate_2_full_round_24<F: Algebra<KoalaBear> + Copy>(
    state: &mut [F; WIDTH_24],
    post_full_round: &mut [&mut F; WIDTH_24],
    round_constants_1: &[KoalaBear; WIDTH_24],
    round_constants_2: &[KoalaBear; WIDTH_24],
) {
    for (state_i, const_i) in state.iter_mut().zip(round_constants_1) {
        *state_i += *const_i;
        *state_i = state_i.cube();
    }
    mds_circ_24(state);

    for (state_i, const_i) in state.iter_mut().zip(round_constants_2.iter()) {
        *state_i += *const_i;
        *state_i = state_i.cube();
    }
    mds_circ_24(state);

    post_full_round.iter_mut().zip(*state).for_each(|(post, x)| {
        **post = x;
    });
}

#[inline]
fn generate_last_2_full_rounds_24<F: Algebra<KoalaBear> + Copy>(
    state: &mut [F; WIDTH_24],
    inputs: &[F; WIDTH_24],
    outputs: &mut [&mut F; POSEIDON_24_OUTPUT_SIZE],
    round_constants_1: &[KoalaBear; WIDTH_24],
    round_constants_2: &[KoalaBear; WIDTH_24],
    is_compress: F,
    is_output_0_9: F,
) {
    for (state_i, const_i) in state.iter_mut().zip(round_constants_1) {
        *state_i += *const_i;
        *state_i = state_i.cube();
    }
    mds_circ_24(state);

    for (state_i, const_i) in state.iter_mut().zip(round_constants_2.iter()) {
        *state_i += *const_i;
        *state_i = state_i.cube();
    }
    mds_circ_24(state);

    // Conditional feedforward: only for compress mode
    for (state_i, input_i) in state.iter_mut().zip(inputs) {
        *state_i += *input_i * is_compress;
    }
    // Select output[0..9] or output[9..18] based on is_output_0_9
    for ((output, first), second) in outputs
        .iter_mut()
        .zip(&state[..POSEIDON_24_OUTPUT_SIZE])
        .zip(&state[POSEIDON_24_OUTPUT_SIZE..][..POSEIDON_24_OUTPUT_SIZE])
    {
        **output = *first * is_output_0_9 + *second * (F::ONE - is_output_0_9);
    }
}
