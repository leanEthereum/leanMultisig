// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use crate::Compression;

pub fn compress<T: Copy + Default, Comp: Compression<[T; WIDTH]>, const CHUNK: usize, const WIDTH: usize>(
    comp: &Comp,
    input: [[T; CHUNK]; 2],
) -> [T; CHUNK] {
    debug_assert!(CHUNK * 2 <= WIDTH);
    let mut state = [T::default(); WIDTH];
    state[..CHUNK].copy_from_slice(&input[0]);
    state[CHUNK..2 * CHUNK].copy_from_slice(&input[1]);
    let out = comp.compress(state);
    out[..CHUNK].try_into().unwrap()
}
