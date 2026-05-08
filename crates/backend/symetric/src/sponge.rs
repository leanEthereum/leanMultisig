// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use crate::Compression;

// IV should have been added to data when necessary (typically: when the length of the data beeing hashed is not constant).
// Sponge construction with capacity = WIDTH - RATE.
// Constraint: data.len() >= WIDTH and (data.len() - WIDTH) is a multiple of RATE.
pub fn hash_slice<T, Comp, const WIDTH: usize, const RATE: usize, const OUT: usize>(comp: &Comp, data: &[T]) -> [T; OUT]
where
    T: Default + Copy,
    Comp: Compression<[T; WIDTH]>,
{
    debug_assert!(OUT <= WIDTH);
    debug_assert!(RATE <= WIDTH);
    debug_assert!(data.len() >= WIDTH);
    debug_assert!((data.len() - WIDTH).is_multiple_of(RATE));
    let mut state: [T; WIDTH] = data[data.len() - WIDTH..].try_into().unwrap();
    comp.compress_mut(&mut state);
    let n_remaining_chunks = (data.len() - WIDTH) / RATE;
    for chunk_idx in (0..n_remaining_chunks).rev() {
        let offset = chunk_idx * RATE;
        state[WIDTH - RATE..].copy_from_slice(&data[offset..offset + RATE]);
        comp.compress_mut(&mut state);
    }
    state[..OUT].try_into().unwrap()
}

/// Precompute sponge state after `n_zero_chunks - 1` zero compresses
/// (1 for initial WIDTH zeros + (n-2) RATE-zero absorbs).
pub fn precompute_zero_suffix_state<T, Comp, const WIDTH: usize, const RATE: usize, const OUT: usize>(
    comp: &Comp,
    n_zero_chunks: usize,
) -> [T; WIDTH]
where
    T: Default + Copy,
    Comp: Compression<[T; WIDTH]>,
{
    debug_assert!(OUT <= WIDTH);
    debug_assert!(RATE <= WIDTH);
    debug_assert!(n_zero_chunks >= 2);
    let mut state = [T::default(); WIDTH];
    comp.compress_mut(&mut state);
    for _ in 0..n_zero_chunks - 2 {
        for s in &mut state[WIDTH - RATE..] {
            *s = T::default();
        }
        comp.compress_mut(&mut state);
    }
    state
}

/// RTL = Right-to-left
#[inline(always)]
pub fn hash_rtl_iter<T, Comp, I, const WIDTH: usize, const RATE: usize, const OUT: usize>(
    comp: &Comp,
    rtl_iter: I,
) -> [T; OUT]
where
    T: Default + Copy,
    Comp: Compression<[T; WIDTH]>,
    I: IntoIterator<Item = T>,
{
    debug_assert!(OUT <= WIDTH);
    debug_assert!(RATE <= WIDTH);
    let mut state = [T::default(); WIDTH];
    let mut iter = rtl_iter.into_iter();
    for pos in (0..WIDTH).rev() {
        state[pos] = iter.next().unwrap();
    }
    comp.compress_mut(&mut state);
    absorb_rtl_chunks::<T, Comp, _, WIDTH, RATE, OUT>(comp, &mut state, &mut iter)
}

/// RTL = Right-to-left
#[inline(always)]
pub fn hash_rtl_iter_with_initial_state<T, Comp, I, const WIDTH: usize, const RATE: usize, const OUT: usize>(
    comp: &Comp,
    mut iter: I,
    initial_state: &[T; WIDTH],
) -> [T; OUT]
where
    T: Default + Copy,
    Comp: Compression<[T; WIDTH]>,
    I: Iterator<Item = T>,
{
    let mut state = *initial_state;
    absorb_rtl_chunks::<T, Comp, _, WIDTH, RATE, OUT>(comp, &mut state, &mut iter)
}

/// RTL = Right-to-left
#[inline(always)]
fn absorb_rtl_chunks<T, Comp, I, const WIDTH: usize, const RATE: usize, const OUT: usize>(
    comp: &Comp,
    state: &mut [T; WIDTH],
    iter: &mut I,
) -> [T; OUT]
where
    T: Default + Copy,
    Comp: Compression<[T; WIDTH]>,
    I: Iterator<Item = T>,
{
    while let Some(elem) = iter.next() {
        state[WIDTH - 1] = elem;
        for pos in (WIDTH - RATE..WIDTH - 1).rev() {
            state[pos] = iter.next().unwrap();
        }
        comp.compress_mut(state);
    }
    state[..OUT].try_into().unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;
    use koala_bear::{KoalaBear, default_koalabear_poseidon1_16};
    use field::PrimeCharacteristicRing;

    /// Verify hash_slice(D) == hash_rtl_iter(D.iter().rev()) for arbitrary D with valid length.
    #[test]
    fn hash_slice_matches_rtl_iter_rate12() {
        let perm = default_koalabear_poseidon1_16();
        // 100 = 16 + 12*7, compatible with WIDTH=16, RATE=12
        let data: Vec<KoalaBear> = (0..100u32).map(|i| KoalaBear::from_u32(i)).collect();
        let h_slice = hash_slice::<KoalaBear, _, 16, 12, 8>(&perm, &data);
        let h_rtl = hash_rtl_iter::<KoalaBear, _, _, 16, 12, 8>(&perm, data.iter().rev().copied());
        assert_eq!(h_slice, h_rtl, "hash_slice and hash_rtl_iter must agree on equivalent inputs");
    }

    /// Same as above but for the existing RATE=8 case.
    #[test]
    fn hash_slice_matches_rtl_iter_rate8() {
        let perm = default_koalabear_poseidon1_16();
        let data: Vec<KoalaBear> = (0..64u32).map(|i| KoalaBear::from_u32(i)).collect();
        let h_slice = hash_slice::<KoalaBear, _, 16, 8, 8>(&perm, &data);
        let h_rtl = hash_rtl_iter::<KoalaBear, _, _, 16, 8, 8>(&perm, data.iter().rev().copied());
        assert_eq!(h_slice, h_rtl, "hash_slice and hash_rtl_iter must agree on equivalent inputs (RATE=8)");
    }
}
