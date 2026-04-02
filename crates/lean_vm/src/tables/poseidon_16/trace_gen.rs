use tracing::instrument;

use crate::{
    F, ZERO_VEC_PTR,
    tables::{Poseidon1Cols16, WIDTH_16, num_cols_poseidon_16},
};
use backend::*;

#[instrument(name = "generate Poseidon16 AIR trace", skip_all)]
pub fn fill_trace_poseidon_16(trace: &mut [Vec<F>]) {
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
        let perm: &mut Poseidon1Cols16<&mut FPacking<F>> =
            unsafe { &mut *(ptrs.as_ptr() as *mut Poseidon1Cols16<&mut FPacking<F>>) };

        generate_trace_rows_for_perm(perm);
    });

    // fill the remaining rows (non packed)
    for i in m..n {
        let ptrs: Vec<*mut F> = trace
            .iter()
            .map(|col| unsafe { (col.as_ptr() as *mut F).add(i) })
            .collect();
        let perm: &mut Poseidon1Cols16<&mut F> = unsafe { &mut *(ptrs.as_ptr() as *mut Poseidon1Cols16<&mut F>) };
        generate_trace_rows_for_perm(perm);
    }
}

pub fn default_poseidon_16_row(null_hash_ptr: usize) -> Vec<F> {
    let mut row = vec![F::ZERO; num_cols_poseidon_16()];
    let ptrs: Vec<*mut F> = (0..num_cols_poseidon_16())
        .map(|i| unsafe { row.as_mut_ptr().add(i) })
        .collect();

    let perm: &mut Poseidon1Cols16<&mut F> = unsafe { &mut *(ptrs.as_ptr() as *mut Poseidon1Cols16<&mut F>) };
    perm.inputs.iter_mut().for_each(|x| **x = F::ZERO);
    *perm.flag = F::ZERO;
    *perm.index_a = F::from_usize(ZERO_VEC_PTR);
    *perm.index_b = F::from_usize(ZERO_VEC_PTR);
    *perm.index_res = F::from_usize(null_hash_ptr);

    generate_trace_rows_for_perm(perm);
    row
}

fn generate_trace_rows_for_perm<F: Algebra<KoalaBear> + Copy>(perm: &mut Poseidon1Cols16<&mut F>) {
    let inputs: [F; WIDTH_16] = std::array::from_fn(|i| *perm.inputs[i]);
    let mut state = inputs;

    // No initial linear layer for Poseidon1 (unlike Poseidon2)

    for (full_round, constants) in perm
        .beginning_full_rounds
        .iter_mut()
        .zip(poseidon1_initial_constants().chunks_exact(2))
    {
        generate_2_full_round(&mut state, full_round, &constants[0], &constants[1]);
    }

    // --- Sparse partial rounds ---
    // Transition: add first-round constants, multiply by m_i
    let frc = poseidon1_sparse_first_round_constants();
    for (s, &c) in state.iter_mut().zip(frc.iter()) {
        *s += c;
    }
    let m_i = poseidon1_sparse_m_i();
    let input_for_mi = state;
    for i in 0..WIDTH_16 {
        let row: [F; WIDTH_16] = m_i[i].map(F::from);
        state[i] = F::dot_product(&input_for_mi, &row);
    }

    let first_rows = poseidon1_sparse_first_row();
    let v_vecs = poseidon1_sparse_v();
    let scalar_rc = poseidon1_sparse_scalar_round_constants();
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
        let row: [F; WIDTH_16] = first_rows[round].map(F::from);
        let new_s0 = F::dot_product(&state, &row);
        state[0] = new_s0;
        for i in 1..WIDTH_16 {
            state[i] += old_s0 * v_vecs[round][i - 1];
        }
    }

    let n_ending_full_rounds = perm.ending_full_rounds.len();
    for (full_round, constants) in perm
        .ending_full_rounds
        .iter_mut()
        .zip(poseidon1_final_constants().chunks_exact(2))
    {
        generate_2_full_round(&mut state, full_round, &constants[0], &constants[1]);
    }

    // Last 2 full rounds with compression (add inputs to outputs)
    generate_last_2_full_rounds(
        &mut state,
        &inputs,
        &mut perm.outputs,
        &poseidon1_final_constants()[2 * n_ending_full_rounds],
        &poseidon1_final_constants()[2 * n_ending_full_rounds + 1],
    );
}

#[inline]
fn generate_2_full_round<F: Algebra<KoalaBear> + Copy>(
    state: &mut [F; WIDTH_16],
    post_full_round: &mut [&mut F; WIDTH_16],
    round_constants_1: &[KoalaBear; WIDTH_16],
    round_constants_2: &[KoalaBear; WIDTH_16],
) {
    for (state_i, const_i) in state.iter_mut().zip(round_constants_1) {
        *state_i += *const_i;
        *state_i = state_i.cube();
    }
    mds_circ_16(state);

    for (state_i, const_i) in state.iter_mut().zip(round_constants_2.iter()) {
        *state_i += *const_i;
        *state_i = state_i.cube();
    }
    mds_circ_16(state);

    post_full_round.iter_mut().zip(*state).for_each(|(post, x)| {
        **post = x;
    });
}

#[inline]
fn generate_last_2_full_rounds<F: Algebra<KoalaBear> + Copy>(
    state: &mut [F; WIDTH_16],
    inputs: &[F; WIDTH_16],
    outputs: &mut [&mut F; WIDTH_16 / 2],
    round_constants_1: &[KoalaBear; WIDTH_16],
    round_constants_2: &[KoalaBear; WIDTH_16],
) {
    for (state_i, const_i) in state.iter_mut().zip(round_constants_1) {
        *state_i += *const_i;
        *state_i = state_i.cube();
    }
    mds_circ_16(state);

    for (state_i, const_i) in state.iter_mut().zip(round_constants_2.iter()) {
        *state_i += *const_i;
        *state_i = state_i.cube();
    }
    mds_circ_16(state);

    // Add inputs to outputs (compression)
    for ((output, state_i), &input_i) in outputs.iter_mut().zip(state).zip(inputs) {
        **output = *state_i + input_i;
    }
}
