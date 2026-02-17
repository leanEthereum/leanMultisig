// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use crate::Permutation;

pub fn compress<T: Copy + Default, Perm: Permutation<[T; WIDTH]>, const CHUNK: usize, const WIDTH: usize>(
    perm: &Perm,
    input: [[T; CHUNK]; 2],
) -> [T; CHUNK] {
    debug_assert!(CHUNK * 2 <= WIDTH);
    let mut state = [T::default(); WIDTH];
    state[..CHUNK].copy_from_slice(&input[0]);
    state[CHUNK..2 * CHUNK].copy_from_slice(&input[1]);
    let out = perm.permute(state);
    out[..CHUNK].try_into().unwrap()
}
