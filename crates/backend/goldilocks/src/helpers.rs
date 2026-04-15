// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

//! Helpers ported from `p3_util` and `p3_field::exponentiation`, scoped to what the
//! Goldilocks field implementation needs.

use field::PrimeCharacteristicRing;

/// Given an element `x` from a 64-bit field `F_P`, compute `x / 2`.
#[inline]
#[must_use]
pub const fn halve_u64<const P: u64>(x: u64) -> u64 {
    let shift = (P + 1) >> 1;
    let half = x >> 1;
    if x & 1 == 0 { half } else { half + shift }
}

/// Inner loop of the binary-GCD-based inversion algorithm used by Goldilocks.
///
/// See https://eprint.iacr.org/2020/972.pdf for background; this mini-GCD builds up
/// a small transformation using u64 ops and bit shifts, which we then apply to the
/// big-int values in the outer loop.
#[inline]
pub const fn gcd_inner<const NUM_ROUNDS: usize>(a: &mut u64, b: &mut u64) -> (i64, i64, i64, i64) {
    let (mut f0, mut g0, mut f1, mut g1) = (1, 0, 0, 1);

    let mut round = 0;
    while round < NUM_ROUNDS {
        if *a & 1 == 0 {
            *a >>= 1;
        } else {
            if *a < *b {
                core::mem::swap(a, b);
                (f0, f1) = (f1, f0);
                (g0, g1) = (g1, g0);
            }
            *a -= *b;
            *a >>= 1;
            f0 -= f1;
            g0 -= g1;
        }
        f1 <<= 1;
        g1 <<= 1;

        round += 1;
    }

    (f0, g0, f1, g1)
}

/// Compute `x -> x^{10540996611094048183}` using a custom addition chain.
///
/// This map computes the seventh root of `x` if `x` is a member of the `Goldilocks` field.
/// It follows from: `7 * 10540996611094048183 = 4*(2^64 - 2^32) + 1 = 1 mod (p - 1)`.
#[must_use]
pub fn exp_10540996611094048183<R: PrimeCharacteristicRing>(val: R) -> R {
    let p1 = val;
    let p10 = p1.square();
    let p11 = p10 * p1;
    let p100 = p10.square();
    let p111 = p100 * p11;
    let p1_30 = p100.exp_power_of_2(30);
    let p1_30_11 = p1_30 * p11;
    let p1_30_11_000 = p1_30_11.exp_power_of_2(3);
    let p1_30_11_011 = p1_30_11_000 * p1_30_11;
    let p1_30_11_011_000000 = p1_30_11_011.exp_power_of_2(6);
    let p_chunk12 = p1_30_11_011_000000 * p1_30_11_011;
    let p_chunk12_000000000000 = p_chunk12.exp_power_of_2(12);
    let p_chunk24 = p_chunk12_000000000000 * p_chunk12;
    let p_chunk24_000000 = p_chunk24.exp_power_of_2(6);
    let p_chunk30 = p_chunk24_000000 * p1_30_11;
    let p_chunk30_0000 = p_chunk30.exp_power_of_2(4);
    p_chunk30_0000 * p111
}
