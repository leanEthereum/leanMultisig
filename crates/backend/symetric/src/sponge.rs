// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use crate::Compression;

// IV should have been added to data when necessary (typically: when the length of the data beeing hashed is not constant). Maybe we should re-add IV all the time for simplicity?
// assumes data length is a multiple of RATE (= 8 in practice).
pub fn hash_slice<T, Comp, const WIDTH: usize, const RATE: usize, const OUT: usize>(comp: &Comp, data: &[T]) -> [T; OUT]
where
    T: Default + Copy,
    Comp: Compression<[T; WIDTH]>,
{
    debug_assert!(RATE == OUT);
    debug_assert!(WIDTH == OUT + RATE);
    debug_assert!(data.len().is_multiple_of(RATE));
    let n_chunks = data.len() / RATE;
    debug_assert!(n_chunks >= 2);
    let mut state: [T; WIDTH] = data[data.len() - WIDTH..].try_into().unwrap();
    comp.compress_mut(&mut state);
    for chunk_idx in (0..n_chunks - 2).rev() {
        let offset = chunk_idx * RATE;
        state[WIDTH - RATE..].copy_from_slice(&data[offset..offset + RATE]);
        comp.compress_mut(&mut state);
    }
    state[..OUT].try_into().unwrap()
}

/// LTR = Left-to-right
#[inline(always)]
pub fn hash_iter<T, Comp, I, const WIDTH: usize, const RATE: usize, const OUT: usize>(
    comp: &Comp,
    iter: I,
) -> [T; OUT]
where
    T: Default + Copy,
    Comp: Compression<[T; WIDTH]>,
    I: IntoIterator<Item = T>,
{
    debug_assert!(RATE == OUT);
    debug_assert!(WIDTH == OUT + RATE);
    let mut state = [T::default(); WIDTH];
    let mut iter = iter.into_iter();
    for s in &mut state {
        *s = iter.next().unwrap();
    }
    comp.compress_mut(&mut state);
    while let Some(elem) = iter.next() {
        state[WIDTH - RATE] = elem;
        for s in &mut state[WIDTH - RATE + 1..] {
            *s = iter.next().unwrap();
        }
        comp.compress_mut(&mut state);
    }
    state[..OUT].try_into().unwrap()
}
