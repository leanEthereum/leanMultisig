// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use crate::Compression;

// T-SPONGE (https://eprint.iacr.org/2014/223)
pub fn hash_iter<T, Comp, I, const WIDTH: usize, const RATE: usize, const OUT: usize>(comp: &Comp, input: I) -> [T; OUT]
where
    T: Default + Copy,
    Comp: Compression<[T; WIDTH]>,
    I: IntoIterator<Item = T>,
{
    let mut state = [T::default(); WIDTH];
    let mut input = input.into_iter();

    for i in 0..WIDTH {
        state[i] = input.next().unwrap_or_default();
    }
    comp.compress_mut(&mut state);

    'outer: loop {
        for i in 0..RATE {
            if let Some(x) = input.next() {
                state[i + (WIDTH - RATE)] = x;
            } else {
                if i != 0 {
                    comp.compress_mut(&mut state);
                }
                break 'outer;
            }
        }
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
    hash_iter::<_, _, _, WIDTH, RATE, OUT>(comp, input.into_iter().flatten().copied())
}

pub fn hash_slice<T, Comp, const WIDTH: usize, const RATE: usize, const OUT: usize>(
    comp: &Comp,
    input: &[T],
) -> [T; OUT]
where
    T: Default + Copy,
    Comp: Compression<[T; WIDTH]>,
{
    hash_iter_slices::<_, _, _, WIDTH, RATE, OUT>(comp, core::iter::once(input))
}
