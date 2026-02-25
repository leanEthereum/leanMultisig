use tracing::instrument;

use crate::{
    F, POSEIDON_16_NULL_HASH_PTR, ZERO_VEC_PTR,
    tables::{PoseidonCols, WIDTH, num_cols_poseidon_16},
};
use backend::*;

#[instrument(name = "generate Poseidon trace", skip_all)]
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
    (0..n / packing_width::<F>()).into_par_iter().for_each(|i| {
        let ptrs: Vec<*mut FPacking<F>> = trace_packed
            .iter()
            .map(|col| unsafe { (col.as_ptr() as *mut FPacking<F>).add(i) })
            .collect();
        let perm: &mut PoseidonCols<&mut FPacking<F>> =
            unsafe { &mut *(ptrs.as_ptr() as *mut PoseidonCols<&mut FPacking<F>>) };

        generate_trace_rows_for_perm(perm);
    });

    // fill the remaining rows (non packed)
    for i in m..n {
        let ptrs: Vec<*mut F> = trace
            .iter()
            .map(|col| unsafe { (col.as_ptr() as *mut F).add(i) })
            .collect();
        let perm: &mut PoseidonCols<&mut F> = unsafe { &mut *(ptrs.as_ptr() as *mut PoseidonCols<&mut F>) };
        generate_trace_rows_for_perm(perm);
    }
}

pub fn default_poseidon_row() -> Vec<F> {
    let mut row = vec![F::ZERO; num_cols_poseidon_16()];
    let ptrs: [*mut F; num_cols_poseidon_16()] = std::array::from_fn(|i| unsafe { row.as_mut_ptr().add(i) });

    let perm: &mut PoseidonCols<&mut F> = unsafe { &mut *(ptrs.as_ptr() as *mut PoseidonCols<&mut F>) };
    perm.inputs.iter_mut().for_each(|x| **x = F::ZERO);
    *perm.flag = F::ZERO;
    *perm.index_a = F::from_usize(ZERO_VEC_PTR);
    *perm.index_b = F::from_usize(ZERO_VEC_PTR);
    *perm.index_res = F::from_usize(POSEIDON_16_NULL_HASH_PTR);

    generate_trace_rows_for_perm(perm);
    row
}

fn generate_trace_rows_for_perm<F: Algebra<KoalaBear> + Copy + 'static>(perm: &mut PoseidonCols<&mut F>) {
    let inputs: [F; WIDTH] = std::array::from_fn(|i| *perm.inputs[i]);
    let mut state = inputs;

    // Poseidon1: NO initial linear layer (unlike Poseidon2)

    let initial_constants = get_poseidon1_initial_constants();
    for (full_round, constants) in perm
        .beginning_full_rounds
        .iter_mut()
        .zip(initial_constants.chunks_exact(2))
    {
        generate_2_full_round(&mut state, full_round, &constants[0], &constants[1]);
    }

    let partial_constants = get_poseidon1_partial_constants();
    for (partial_round, constants) in perm.partial_rounds.iter_mut().zip(partial_constants) {
        generate_partial_round(&mut state, partial_round, constants);
    }

    let n_ending_full_rounds = perm.ending_full_rounds.len();
    let final_constants = get_poseidon1_final_constants();
    for (full_round, constants) in perm.ending_full_rounds.iter_mut().zip(final_constants.chunks_exact(2)) {
        generate_2_full_round(&mut state, full_round, &constants[0], &constants[1]);
    }

    // Last 2 full rounds with compression (add inputs to outputs)
    generate_last_2_full_rounds(
        &mut state,
        &inputs,
        &mut perm.outputs,
        &final_constants[2 * n_ending_full_rounds],
        &final_constants[2 * n_ending_full_rounds + 1],
    );
}

#[inline]
fn generate_2_full_round<F: Algebra<KoalaBear> + Copy + 'static>(
    state: &mut [F; WIDTH],
    post_full_round: &mut [&mut F; WIDTH],
    round_constants_1: &[KoalaBear; WIDTH],
    round_constants_2: &[KoalaBear; WIDTH],
) {
    for (state_i, const_i) in state.iter_mut().zip(round_constants_1) {
        *state_i += *const_i;
        *state_i = state_i.cube();
    }
    mds_circulant_16_karatsuba(state);

    for (state_i, const_i) in state.iter_mut().zip(round_constants_2.iter()) {
        *state_i += *const_i;
        *state_i = state_i.cube();
    }
    mds_circulant_16_karatsuba(state);

    post_full_round.iter_mut().zip(*state).for_each(|(post, x)| {
        **post = x;
    });
}

#[inline]
fn generate_last_2_full_rounds<F: Algebra<KoalaBear> + Copy + 'static>(
    state: &mut [F; WIDTH],
    inputs: &[F; WIDTH],
    outputs: &mut [&mut F; WIDTH / 2],
    round_constants_1: &[KoalaBear; WIDTH],
    round_constants_2: &[KoalaBear; WIDTH],
) {
    for (state_i, const_i) in state.iter_mut().zip(round_constants_1) {
        *state_i += *const_i;
        *state_i = state_i.cube();
    }
    mds_circulant_16_karatsuba(state);

    for (state_i, const_i) in state.iter_mut().zip(round_constants_2.iter()) {
        *state_i += *const_i;
        *state_i = state_i.cube();
    }
    mds_circulant_16_karatsuba(state);

    // Add inputs to outputs (compression)
    for ((output, state_i), &input_i) in outputs.iter_mut().zip(state).zip(inputs) {
        **output = *state_i + input_i;
    }
}

/// Poseidon1 partial round: add constants to ALL 16 elements, cube state[0], apply MDS.
#[inline]
fn generate_partial_round<F: Algebra<KoalaBear> + Copy + 'static>(
    state: &mut [F; WIDTH],
    post_partial_round: &mut F,
    round_constants: &[KoalaBear; WIDTH],
) {
    // Add round constants to ALL elements (Poseidon1 difference from Poseidon2)
    for (state_i, &const_i) in state.iter_mut().zip(round_constants.iter()) {
        *state_i += const_i;
    }
    state[0] = state[0].cube();
    *post_partial_round = state[0];
    mds_circulant_16_karatsuba(state);
}
