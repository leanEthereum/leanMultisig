use p3_poseidon2::GenericPoseidon2LinearLayers;
use tracing::instrument;

use crate::{
    F,  POSEIDON_24_NULL_HASH_PTR, VECTOR_LEN, ZERO_VEC_PTR, tables::{Poseidon24Cols, WIDTH_24, num_cols_24}
};
use multilinear_toolkit::prelude::*;
use p3_koala_bear::{
    GenericPoseidon2LinearLayersKoalaBear, KOALABEAR_RC24_EXTERNAL_FINAL, KOALABEAR_RC24_EXTERNAL_INITIAL,
    KOALABEAR_RC24_INTERNAL, KoalaBear,
};

#[instrument(name = "generate Poseidon2 trace 24", skip_all)]
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
    (0..n / packing_width::<F>()).into_par_iter().for_each(|i| {
        let ptrs: Vec<*mut FPacking<F>> = trace_packed
            .iter()
            .map(|col| unsafe { (col.as_ptr() as *mut FPacking<F>).add(i) })
            .collect();
        let perm: &mut Poseidon24Cols<&mut FPacking<F>> =
            unsafe { &mut *(ptrs.as_ptr() as *mut Poseidon24Cols<&mut FPacking<F>>) };

        generate_trace_rows_for_perm(perm);
    });

    // fill the remaining rows (non packed)
    for i in m..n {
        let ptrs: Vec<*mut F> = trace
            .iter()
            .map(|col| unsafe { (col.as_ptr() as *mut F).add(i) })
            .collect();
        let perm: &mut Poseidon24Cols<&mut F> = unsafe { &mut *(ptrs.as_ptr() as *mut Poseidon24Cols<&mut F>) };
        generate_trace_rows_for_perm(perm);
    }
}

pub fn default_poseidon_24_row() -> Vec<F> {
    let mut row = vec![F::ZERO; num_cols_24()];
    let ptrs: [*mut F; num_cols_24()] = std::array::from_fn(|i| unsafe { row.as_mut_ptr().add(i) });

    let perm: &mut Poseidon24Cols<&mut F> = unsafe { &mut *(ptrs.as_ptr() as *mut Poseidon24Cols<&mut F>) };
    perm.inputs.iter_mut().for_each(|x| **x = F::ZERO);
    *perm.flag = F::ZERO;
    *perm.index_a = F::from_usize(ZERO_VEC_PTR);
    *perm.index_a_bis = F::from_usize(ZERO_VEC_PTR + VECTOR_LEN);
    *perm.index_b = F::from_usize(ZERO_VEC_PTR);
    *perm.index_res = F::from_usize(POSEIDON_24_NULL_HASH_PTR);
    *perm.index_res_bis = F::from_usize(POSEIDON_24_NULL_HASH_PTR + VECTOR_LEN);
    *perm.index_res_bis_bis = F::from_usize(POSEIDON_24_NULL_HASH_PTR + 2 * VECTOR_LEN);

    generate_trace_rows_for_perm(perm);
    row
}
fn generate_trace_rows_for_perm<F: Algebra<KoalaBear> + Copy>(perm: &mut Poseidon24Cols<&mut F>) {
    let mut state: [F; WIDTH_24] = std::array::from_fn(|i| *perm.inputs[i]);

    GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(&mut state);

    for (full_round, constants) in perm
        .beginning_full_rounds
        .iter_mut()
        .zip(KOALABEAR_RC24_EXTERNAL_INITIAL.chunks_exact(2))
    {
        generate_full_round(&mut state, full_round, &constants[0], &constants[1]);
    }

    for (partial_round, constant) in perm.partial_rounds.iter_mut().zip(&KOALABEAR_RC24_INTERNAL) {
        generate_partial_round(&mut state, partial_round, *constant);
    }

    for (full_round, constants) in perm
        .ending_full_rounds
        .iter_mut()
        .zip(KOALABEAR_RC24_EXTERNAL_FINAL.chunks_exact(2))
    {
        generate_full_round(&mut state, full_round, &constants[0], &constants[1]);
    }
}

#[inline]
fn generate_full_round<F: Algebra<KoalaBear> + Copy>(
    state: &mut [F; WIDTH_24],
    post_full_round: &mut [&mut F; WIDTH_24],
    round_constants_1: &[KoalaBear; WIDTH_24],
    round_constants_2: &[KoalaBear; WIDTH_24],
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
fn generate_partial_round<F: Algebra<KoalaBear> + Copy>(
    state: &mut [F; WIDTH_24],
    post_partial_round: &mut F,
    round_constant: KoalaBear,
) {
    state[0] += round_constant;
    state[0] = state[0].cube();
    *post_partial_round = state[0];
    GenericPoseidon2LinearLayersKoalaBear::internal_linear_layer(state);
}
