// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use crate::Compression;

// T-SPONGE (https://eprint.iacr.org/2014/223)
// Right-to-left: processes chunks from the end so trailing zeros are absorbed first.
pub fn hash_iter<T, Comp, I, const WIDTH: usize, const RATE: usize, const OUT: usize>(comp: &Comp, input: I) -> [T; OUT]
where
    T: Default + Copy,
    Comp: Compression<[T; WIDTH]>,
    I: IntoIterator<Item = T>,
{
    let data: Vec<T> = input.into_iter().collect();
    hash_data::<T, Comp, WIDTH, RATE, OUT>(comp, &data)
}

fn hash_data<T, Comp, const WIDTH: usize, const RATE: usize, const OUT: usize>(comp: &Comp, data: &[T]) -> [T; OUT]
where
    T: Default + Copy,
    Comp: Compression<[T; WIDTH]>,
{
    debug_assert!(RATE == OUT);
    debug_assert!(WIDTH == OUT + RATE);

    let n_chunks = data.len() / RATE;
    debug_assert!(n_chunks >= 2);
    let mut state: [T; WIDTH] = data[data.len() - WIDTH..].try_into().unwrap();
    comp.compress_mut(&mut state);

    // Fold remaining chunks right to left
    for chunk_idx in (0..n_chunks - 2).rev() {
        let offset = chunk_idx * RATE;
        state[WIDTH - RATE..].copy_from_slice(&data[offset..offset + RATE]);
        comp.compress_mut(&mut state);
    }

    state[..OUT].try_into().unwrap()
}

pub fn hash_iter_slices<'a, T, Comp, I, const WIDTH: usize, const RATE: usize, const OUT: usize>(
    comp: &Comp,
    input: I,
) -> [T; OUT]
where
    T: Default + Copy + 'a,
    Comp: Compression<[T; WIDTH]>,
    I: IntoIterator<Item = &'a [T]>,
{
    let data: Vec<T> = input.into_iter().flatten().copied().collect();
    hash_data::<T, Comp, WIDTH, RATE, OUT>(comp, &data)
}

pub fn hash_slice<T, Comp, const WIDTH: usize, const RATE: usize, const OUT: usize>(
    comp: &Comp,
    input: &[T],
) -> [T; OUT]
where
    T: Default + Copy,
    Comp: Compression<[T; WIDTH]>,
{
    hash_data::<T, Comp, WIDTH, RATE, OUT>(comp, input)
}
