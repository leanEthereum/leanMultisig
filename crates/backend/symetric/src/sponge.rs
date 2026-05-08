// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use field::PrimeCharacteristicRing;

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

// =============================================================================
// MMO-mode (Davies-Meyer / Matyas-Meyer-Oseas) feedforward sponge
// =============================================================================
//
// Standard PaddingFreeSponge ("oSponge") collision security is c·log2(p)/2 bits
// because of the inner-state birthday attack on the capacity portion. With
// (WIDTH=16, RATE=12, capacity=4) over KoalaBear (p ~= 2^31), that bound is
// 4*31/2 = 62 bits — short of the 124-bit target.
//
// This MMO variant treats each absorb step as the Matyas-Meyer-Oseas
// compression F(state, M) = state + perm(state + (M, 0_cap)), i.e. message is
// ADDED into the rate positions (not overwritten) and the full pre-perm state
// is fed forward. The chaining variable is then the FULL 16-element state
// (496 bits), not the 4-element capacity, so generic compression collision is
// 2^{b/2} = 2^248 in the random-permutation model, and after truncation to
// OUT=8 elements the digest birthday gives 2^{output_bits/2} = 2^124.
//
// IMPORTANT: `Compression::compress_mut` for Poseidon-16 in this codebase ALREADY
// computes `output = perm(input) + input` (matching the AIR's `eval_last_2_full_rounds_16`
// which adds initial state to post-perm state — see lean_vm/src/tables/poseidon_16/mod.rs).
// So a single `compress_mut` call IS one MMO step; we must NOT add `prev` again
// after, or we'd double-feedforward and disagree with the zk-DSL precompile.
//
// Convention matches the existing hash_slice: the first 16 elements of data
// are loaded directly into the state and the precompile is invoked once
// (zero IV implicit). Subsequent RATE-sized blocks are absorbed with ADD into
// rate positions, then a single compression invocation gives the next state.

/// MMO-mode (feedforward) variant of `hash_slice`. Same input format and
/// alignment requirements; collision security is bounded by the digest size
/// rather than the capacity.
pub fn mmo_hash_slice<T, Comp, const WIDTH: usize, const RATE: usize, const OUT: usize>(comp: &Comp, data: &[T]) -> [T; OUT]
where
    T: PrimeCharacteristicRing,
    Comp: Compression<[T; WIDTH]>,
{
    debug_assert!(OUT <= WIDTH);
    debug_assert!(RATE <= WIDTH);
    debug_assert!(data.len() >= WIDTH);
    debug_assert!((data.len() - WIDTH).is_multiple_of(RATE));
    let mut state: [T; WIDTH] = data[data.len() - WIDTH..].try_into().unwrap();
    // First MMO compression: state ← perm(state) + state (compress_mut already does this).
    comp.compress_mut(&mut state);
    let n_remaining_chunks = (data.len() - WIDTH) / RATE;
    for chunk_idx in (0..n_remaining_chunks).rev() {
        let offset = chunk_idx * RATE;
        // ADD message into rate positions (not overwrite).
        for i in 0..RATE {
            state[WIDTH - RATE + i] += data[offset + i];
        }
        // One MMO compression: state ← perm(state) + state. compress_mut already
        // performs the full-state feedforward.
        comp.compress_mut(&mut state);
    }
    state[..OUT].try_into().unwrap()
}

/// MMO-mode variant of `precompute_zero_suffix_state`. Same number of perm
/// calls as the standard variant (n_zero_chunks - 1 total).
pub fn mmo_precompute_zero_suffix_state<T, Comp, const WIDTH: usize, const RATE: usize, const OUT: usize>(
    comp: &Comp,
    n_zero_chunks: usize,
) -> [T; WIDTH]
where
    T: PrimeCharacteristicRing,
    Comp: Compression<[T; WIDTH]>,
{
    debug_assert!(OUT <= WIDTH);
    debug_assert!(RATE <= WIDTH);
    debug_assert!(n_zero_chunks >= 2);
    let mut state = [T::ZERO; WIDTH];
    // First absorb (16 zeros). compress_mut applies one MMO compression.
    comp.compress_mut(&mut state);
    // Subsequent (n_zero_chunks - 2) absorbs of zero RATE-chunks. ADD 0 is a
    // no-op, so each iteration is just one MMO compression.
    for _ in 0..n_zero_chunks - 2 {
        comp.compress_mut(&mut state);
    }
    state
}

/// RTL = Right-to-left. MMO-mode counterpart of `hash_rtl_iter`.
#[inline(always)]
pub fn mmo_hash_rtl_iter<T, Comp, I, const WIDTH: usize, const RATE: usize, const OUT: usize>(
    comp: &Comp,
    rtl_iter: I,
) -> [T; OUT]
where
    T: PrimeCharacteristicRing,
    Comp: Compression<[T; WIDTH]>,
    I: IntoIterator<Item = T>,
{
    debug_assert!(OUT <= WIDTH);
    debug_assert!(RATE <= WIDTH);
    let mut state = [T::ZERO; WIDTH];
    let mut iter = rtl_iter.into_iter();
    for pos in (0..WIDTH).rev() {
        state[pos] = iter.next().unwrap();
    }
    comp.compress_mut(&mut state);
    mmo_absorb_rtl_chunks::<T, Comp, _, WIDTH, RATE, OUT>(comp, &mut state, &mut iter)
}

/// RTL = Right-to-left. MMO-mode counterpart of `hash_rtl_iter_with_initial_state`.
#[inline(always)]
pub fn mmo_hash_rtl_iter_with_initial_state<T, Comp, I, const WIDTH: usize, const RATE: usize, const OUT: usize>(
    comp: &Comp,
    mut iter: I,
    initial_state: &[T; WIDTH],
) -> [T; OUT]
where
    T: PrimeCharacteristicRing,
    Comp: Compression<[T; WIDTH]>,
    I: Iterator<Item = T>,
{
    let mut state = *initial_state;
    mmo_absorb_rtl_chunks::<T, Comp, _, WIDTH, RATE, OUT>(comp, &mut state, &mut iter)
}

/// RTL = Right-to-left. MMO-mode chunk absorption: ADD message into rate, then
/// one MMO compression (compress_mut already does perm + input feedforward).
#[inline(always)]
fn mmo_absorb_rtl_chunks<T, Comp, I, const WIDTH: usize, const RATE: usize, const OUT: usize>(
    comp: &Comp,
    state: &mut [T; WIDTH],
    iter: &mut I,
) -> [T; OUT]
where
    T: PrimeCharacteristicRing,
    Comp: Compression<[T; WIDTH]>,
    I: Iterator<Item = T>,
{
    while let Some(elem) = iter.next() {
        // ADD into rate positions (last RATE elements), reading the iterator
        // from right to left.
        state[WIDTH - 1] += elem;
        for pos in (WIDTH - RATE..WIDTH - 1).rev() {
            state[pos] += iter.next().unwrap();
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

    /// MMO-mode counterpart of hash_slice_matches_rtl_iter_rate12.
    #[test]
    fn mmo_hash_slice_matches_rtl_iter_rate12() {
        let perm = default_koalabear_poseidon1_16();
        let data: Vec<KoalaBear> = (0..100u32).map(|i| KoalaBear::from_u32(i)).collect();
        let h_slice = mmo_hash_slice::<KoalaBear, _, 16, 12, 8>(&perm, &data);
        let h_rtl = mmo_hash_rtl_iter::<KoalaBear, _, _, 16, 12, 8>(&perm, data.iter().rev().copied());
        assert_eq!(h_slice, h_rtl, "mmo_hash_slice and mmo_hash_rtl_iter must agree on equivalent inputs");
    }

    /// MMO-mode is structurally distinct from oSponge — verify they produce
    /// different digests on the same input (sanity check that we are not
    /// accidentally falling back to the standard sponge).
    #[test]
    fn mmo_differs_from_standard_sponge() {
        let perm = default_koalabear_poseidon1_16();
        let data: Vec<KoalaBear> = (0..28u32).map(|i| KoalaBear::from_u32(i)).collect(); // 16 + 12, two-block input
        let h_std = hash_slice::<KoalaBear, _, 16, 12, 8>(&perm, &data);
        let h_mmo = mmo_hash_slice::<KoalaBear, _, 16, 12, 8>(&perm, &data);
        assert_ne!(h_std, h_mmo, "MMO must differ from standard sponge for multi-block inputs");
    }

    /// Verify the MMO precompute is consistent with directly hashing zeros.
    #[test]
    fn mmo_precompute_zero_suffix_matches_full_zero_hash() {
        let perm = default_koalabear_poseidon1_16();
        let n_zero_chunks: usize = 4; // WIDTH absorb + 3 RATE absorbs of zero
        let zeros: Vec<KoalaBear> =
            std::iter::repeat_n(KoalaBear::ZERO, 16 + 12 * (n_zero_chunks - 1)).collect();
        let direct = mmo_hash_slice::<KoalaBear, _, 16, 12, 8>(&perm, &zeros);
        let pre = mmo_precompute_zero_suffix_state::<KoalaBear, _, 16, 12, 8>(&perm, n_zero_chunks);
        // The precompute does (n_zero_chunks - 1) MMO compressions; mmo_hash_slice
        // does n_zero_chunks total. To finalize we need ONE MORE compression
        // (ADDing zero rate is a no-op).
        let mut state = pre;
        perm.compress_mut(&mut state);
        let advanced: [KoalaBear; 8] = state[..8].try_into().unwrap();
        assert_eq!(advanced, direct);
    }
}
