use p3_poseidon2::GenericPoseidon2LinearLayers;
use tracing::instrument;
use utils::assert_eq_many;

use crate::{
    F, POSEIDON_16_DEFAULT_COMPRESSION, POSEIDON_16_NULL_HASH_PTR, ZERO_VEC_PTR,
    tables::{Poseidon2Cols, WIDTH, num_cols},
};
use multilinear_toolkit::prelude::*;
use p3_koala_bear::{
    GenericPoseidon2LinearLayersKoalaBear, KOALABEAR_RC16_EXTERNAL_FINAL, KOALABEAR_RC16_EXTERNAL_INITIAL,
    KOALABEAR_RC16_INTERNAL, KoalaBear,
};

#[instrument(name = "generate Poseidon2 trace", skip_all)]
pub fn generate_trace_rows_16(
    inputs: &[Vec<F>; WIDTH],
    index_a: &[F],
    index_b: &[F],
    index_res: &[F],
    compress: &[F],
) -> Vec<Vec<F>> {
    // return columns padded to the next power of two
    let n = inputs[0].len();
    assert!(inputs.iter().all(|col| col.len() == n));
    assert_eq_many!(index_a.len(), index_b.len(), index_res.len(), compress.len(), n);

    let mut res = (0..num_cols())
        .map(|_| unsafe { uninitialized_vec::<F>(n.next_power_of_two()) })
        .collect::<Vec<_>>();
    let m = n - (n % packing_width::<F>());
    let inputs_packed: [_; WIDTH] = std::array::from_fn(|i| FPacking::<F>::pack_slice(&inputs[i][..m]));
    let index_a_packed = FPacking::<F>::pack_slice(&index_a[..m]);
    let index_b_packed = FPacking::<F>::pack_slice(&index_b[..m]);
    let index_res_packed = FPacking::<F>::pack_slice(&index_res[..m]);
    let compress_packed = FPacking::<F>::pack_slice(&compress[..m]);
    let res_packed: Vec<_> = res.iter().map(|col| FPacking::<F>::pack_slice(&col[..m])).collect();

    // fill the packed rows
    (0..n / packing_width::<F>()).into_par_iter().for_each(|i| {
        let state: [_; WIDTH] = std::array::from_fn(|j| inputs_packed[j][i]);
        let ptrs: Vec<*mut FPacking<F>> = res_packed
            .iter()
            .map(|col| unsafe { (col.as_ptr() as *mut FPacking<F>).add(i) })
            .collect();
        let perm: &mut Poseidon2Cols<&mut FPacking<F>> =
            unsafe { &mut *(ptrs.as_ptr() as *mut Poseidon2Cols<&mut FPacking<F>>) };

        generate_trace_rows_for_perm(
            perm,
            FPacking::<F>::ONE,
            index_a_packed[i],
            index_b_packed[i],
            index_res_packed[i],
            compress_packed[i],
            state,
        );
    });

    // fill the remaining rows (non packed)
    for i in m..n {
        let state: [F; WIDTH] = std::array::from_fn(|j| inputs[j][i]);
        let ptrs: Vec<*mut F> = res
            .iter()
            .map(|col| unsafe { (col.as_ptr() as *mut F).add(i) })
            .collect();
        let perm: &mut Poseidon2Cols<&mut F> = unsafe { &mut *(ptrs.as_ptr() as *mut Poseidon2Cols<&mut F>) };
        generate_trace_rows_for_perm(perm, F::ONE, index_a[i], index_b[i], index_res[i], compress[i], state);
    }

    // fill the padding rows
    res.par_iter_mut().zip(default_poseidon_row()).for_each(|(col, v)| {
        col[n..].fill(v);
    });

    res
}

pub fn default_poseidon_row() -> Vec<F> {
    let mut row = vec![F::ZERO; num_cols()];
    let ptrs: [*mut F; num_cols()] = std::array::from_fn(|i| unsafe { row.as_mut_ptr().add(i) });

    let perm: &mut Poseidon2Cols<&mut F> = unsafe { &mut *(ptrs.as_ptr() as *mut Poseidon2Cols<&mut F>) };

    generate_trace_rows_for_perm(
        perm,
        F::ZERO,
        F::from_usize(ZERO_VEC_PTR),
        F::from_usize(ZERO_VEC_PTR),
        F::from_usize(POSEIDON_16_NULL_HASH_PTR),
        F::from_bool(POSEIDON_16_DEFAULT_COMPRESSION),
        [F::ZERO; WIDTH],
    );
    row
}
fn generate_trace_rows_for_perm<F: Algebra<KoalaBear> + Copy>(
    perm: &mut Poseidon2Cols<&mut F>,
    flag: F,
    index_a: F,
    index_b: F,
    index_res: F,
    compress: F,
    mut state: [F; WIDTH],
) {
    *perm.flag = flag;
    *perm.index_a = index_a;
    *perm.index_b = index_b;
    *perm.index_res = index_res;
    *perm.index_res_bis = (F::ONE - compress) * (index_res + F::ONE);
    *perm.compress = compress;
    perm.inputs.iter_mut().zip(state.iter()).for_each(|(input, &x)| {
        **input = x;
    });

    GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(&mut state);

    for (full_round, constants) in perm
        .beginning_full_rounds
        .iter_mut()
        .zip(KOALABEAR_RC16_EXTERNAL_INITIAL.chunks_exact(2))
    {
        generate_full_round(&mut state, full_round, &constants[0], &constants[1]);
    }

    for (partial_round, constant) in perm.partial_rounds.iter_mut().zip(&KOALABEAR_RC16_INTERNAL) {
        generate_partial_round(&mut state, partial_round, *constant);
    }

    for (full_round, constants) in perm
        .ending_full_rounds
        .iter_mut()
        .zip(KOALABEAR_RC16_EXTERNAL_FINAL.chunks_exact(2))
    {
        generate_full_round(&mut state, full_round, &constants[0], &constants[1]);
    }

    perm.ending_full_rounds.last_mut().unwrap()[8..16]
        .iter_mut()
        .for_each(|x| {
            **x = (F::ONE - compress) * **x;
        });
}

#[inline]
fn generate_full_round<F: Algebra<KoalaBear> + Copy>(
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
