// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use crate::Permutation;

pub fn hash_iter<T, Perm, I, const WIDTH: usize, const RATE: usize, const OUT: usize>(perm: &Perm, input: I) -> [T; OUT]
where
    T: Default + Copy,
    Perm: Permutation<[T; WIDTH]>,
    I: IntoIterator<Item = T>,
{
    let mut state = [T::default(); WIDTH];
    let mut input = input.into_iter();

    for i in 0..WIDTH {
        state[i] = input.next().unwrap_or_default();
    }
    perm.permute_mut(&mut state);

    'outer: loop {
        for i in 0..RATE {
            if let Some(x) = input.next() {
                state[i + (WIDTH - RATE)] = x;
            } else {
                if i != 0 {
                    perm.permute_mut(&mut state);
                }
                break 'outer;
            }
        }
        perm.permute_mut(&mut state);
    }

    state[..OUT].try_into().unwrap()
}

pub fn hash_iter_slices<'a, T, Perm, I, const WIDTH: usize, const RATE: usize, const OUT: usize>(
    perm: &Perm,
    input: I,
) -> [T; OUT]
where
    T: Default + Copy + 'a,
    Perm: Permutation<[T; WIDTH]>,
    I: IntoIterator<Item = &'a [T]>,
{
    hash_iter::<_, _, _, WIDTH, RATE, OUT>(perm, input.into_iter().flatten().copied())
}

pub fn hash_slice<T, Perm, const WIDTH: usize, const RATE: usize, const OUT: usize>(
    perm: &Perm,
    input: &[T],
) -> [T; OUT]
where
    T: Default + Copy,
    Perm: Permutation<[T; WIDTH]>,
{
    hash_iter_slices::<_, _, _, WIDTH, RATE, OUT>(perm, core::iter::once(input))
}
