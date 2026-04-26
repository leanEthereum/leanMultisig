// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use alloc::vec::Vec;
use core::arch::x86_64::*;
use core::fmt::Debug;
use core::iter::{Product, Sum};
use core::mem::transmute;
use core::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use field::interleave::{interleave_u64, interleave_u128, interleave_u256};
use field::op_assign_macros::{
    impl_add_assign, impl_add_base_field, impl_div_methods, impl_mul_base_field, impl_mul_methods, impl_packed_value,
    impl_rng, impl_sub_assign, impl_sub_base_field, impl_sum_prod_base_field, ring_sum,
};
use field::{
    Algebra, Field, InjectiveMonomial, PackedField, PackedFieldPow2, PackedValue, PermutationMonomial,
    PrimeCharacteristicRing, PrimeField64, impl_packed_field_pow_2,
};
use rand::Rng;
use rand::distr::{Distribution, StandardUniform};
use utils::reconstitute_from_base;

use crate::helpers::exp_10540996611094048183;
use crate::{Goldilocks, P};

const WIDTH: usize = 8;

/// Vectorized AVX512 implementation of `Goldilocks` arithmetic.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
#[repr(transparent)] // Needed to make `transmute`s safe.
#[must_use]
pub struct PackedGoldilocksAVX512(pub [Goldilocks; WIDTH]);

impl PackedGoldilocksAVX512 {
    /// Get an arch-specific vector representing the packed values.
    #[inline]
    #[must_use]
    pub(crate) fn to_vector(self) -> __m512i {
        unsafe { transmute(self) }
    }

    /// Make a packed field vector from an arch-specific vector.
    ///
    /// Goldilocks elements may be arbitrary u64s, so this is always safe.
    #[inline]
    pub(crate) fn from_vector(vector: __m512i) -> Self {
        unsafe { transmute(vector) }
    }

    /// Copy `value` to all positions in a packed vector. `const` version of `From<Goldilocks>`.
    #[inline]
    const fn broadcast(value: Goldilocks) -> Self {
        Self([value; WIDTH])
    }
}

impl From<Goldilocks> for PackedGoldilocksAVX512 {
    fn from(x: Goldilocks) -> Self {
        Self::broadcast(x)
    }
}

impl Add for PackedGoldilocksAVX512 {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        Self::from_vector(add(self.to_vector(), rhs.to_vector()))
    }
}

impl Sub for PackedGoldilocksAVX512 {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Self) -> Self {
        Self::from_vector(sub(self.to_vector(), rhs.to_vector()))
    }
}

impl Neg for PackedGoldilocksAVX512 {
    type Output = Self;
    #[inline]
    fn neg(self) -> Self {
        Self::from_vector(neg(self.to_vector()))
    }
}

impl Mul for PackedGoldilocksAVX512 {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        Self::from_vector(mul(self.to_vector(), rhs.to_vector()))
    }
}

impl_add_assign!(PackedGoldilocksAVX512);
impl_sub_assign!(PackedGoldilocksAVX512);
impl_mul_methods!(PackedGoldilocksAVX512);
ring_sum!(PackedGoldilocksAVX512);
impl_rng!(PackedGoldilocksAVX512);

impl PrimeCharacteristicRing for PackedGoldilocksAVX512 {
    type PrimeSubfield = Goldilocks;

    const ZERO: Self = Self::broadcast(Goldilocks::ZERO);
    const ONE: Self = Self::broadcast(Goldilocks::ONE);
    const TWO: Self = Self::broadcast(Goldilocks::TWO);
    const NEG_ONE: Self = Self::broadcast(Goldilocks::NEG_ONE);

    #[inline]
    fn from_prime_subfield(f: Self::PrimeSubfield) -> Self {
        f.into()
    }

    #[inline]
    fn halve(&self) -> Self {
        Self::from_vector(halve(self.to_vector()))
    }

    #[inline]
    fn square(&self) -> Self {
        Self::from_vector(square(self.to_vector()))
    }

    #[inline]
    fn zero_vec(len: usize) -> Vec<Self> {
        // SAFETY: this is a repr(transparent) wrapper around an array.
        unsafe { reconstitute_from_base(Goldilocks::zero_vec(len * WIDTH)) }
    }
}

impl_add_base_field!(PackedGoldilocksAVX512, Goldilocks);
impl_sub_base_field!(PackedGoldilocksAVX512, Goldilocks);
impl_mul_base_field!(PackedGoldilocksAVX512, Goldilocks);
impl_div_methods!(PackedGoldilocksAVX512, Goldilocks);
impl_sum_prod_base_field!(PackedGoldilocksAVX512, Goldilocks);

impl Algebra<Goldilocks> for PackedGoldilocksAVX512 {}

impl InjectiveMonomial<7> for PackedGoldilocksAVX512 {}

impl PermutationMonomial<7> for PackedGoldilocksAVX512 {
    fn injective_exp_root_n(&self) -> Self {
        exp_10540996611094048183(*self)
    }
}

impl_packed_value!(PackedGoldilocksAVX512, Goldilocks, WIDTH);

unsafe impl PackedField for PackedGoldilocksAVX512 {
    type Scalar = Goldilocks;
}

impl_packed_field_pow_2!(
    PackedGoldilocksAVX512;
    [
        (1, interleave_u64),
        (2, interleave_u128),
        (4, interleave_u256),
    ],
    WIDTH
);

const FIELD_ORDER: __m512i = unsafe { transmute([Goldilocks::ORDER_U64; WIDTH]) };
const EPSILON: __m512i = unsafe { transmute([Goldilocks::ORDER_U64.wrapping_neg(); WIDTH]) };

#[inline]
unsafe fn canonicalize(x: __m512i) -> __m512i {
    // For `x < ORDER`, `x - ORDER` underflows to a huge u64, so `min` picks the
    // original. For `x >= ORDER`, `x - ORDER` is the canonical form (smaller),
    // so `min` picks it. One sub + one min instead of cmpge + masked sub.
    unsafe { _mm512_min_epu64(x, _mm512_sub_epi64(x, FIELD_ORDER)) }
}

/// Compute `x + y mod P`. Result may be > P.
///
/// # Safety
/// Caller must ensure `x + y < 2^64 + P`.
#[inline]
unsafe fn add_no_double_overflow_64_64(x: __m512i, y: __m512i) -> __m512i {
    unsafe {
        let res_wrapped = _mm512_add_epi64(x, y);
        let mask = _mm512_cmplt_epu64_mask(res_wrapped, y);
        _mm512_mask_sub_epi64(res_wrapped, mask, res_wrapped, FIELD_ORDER)
    }
}

/// Compute `x - y mod P`. Result may be > P.
///
/// # Safety
/// Caller must ensure `x - y > -P`.
#[inline]
unsafe fn sub_no_double_overflow_64_64(x: __m512i, y: __m512i) -> __m512i {
    unsafe {
        let mask = _mm512_cmplt_epu64_mask(x, y);
        let res_wrapped = _mm512_sub_epi64(x, y);
        _mm512_mask_add_epi64(res_wrapped, mask, res_wrapped, FIELD_ORDER)
    }
}

#[inline]
fn add(x: __m512i, y: __m512i) -> __m512i {
    unsafe { add_no_double_overflow_64_64(x, canonicalize(y)) }
}

#[inline]
fn sub(x: __m512i, y: __m512i) -> __m512i {
    unsafe { sub_no_double_overflow_64_64(x, canonicalize(y)) }
}

#[inline]
fn neg(y: __m512i) -> __m512i {
    unsafe { _mm512_sub_epi64(FIELD_ORDER, canonicalize(y)) }
}

/// Halve a vector of Goldilocks field elements.
#[inline(always)]
pub(crate) fn halve(input: __m512i) -> __m512i {
    // For val in [0, P): val even -> val/2 = val>>1; val odd -> (val+P)/2 = (val>>1) + (P+1)/2.
    unsafe {
        const ONE: __m512i = unsafe { transmute([1_i64; 8]) };
        let half = _mm512_set1_epi64(P.div_ceil(2) as i64);

        let least_bit = _mm512_test_epi64_mask(input, ONE);
        let t = _mm512_srli_epi64::<1>(input);
        _mm512_mask_add_epi64(t, least_bit, t, half)
    }
}

#[allow(clippy::useless_transmute)]
const LO_32_BITS_MASK: __mmask16 = unsafe { transmute(0b0101010101010101u16) };

/// Full 64x64 -> 128 multiplication, returning `(hi, lo)`.
#[inline]
fn mul64_64(x: __m512i, y: __m512i) -> (__m512i, __m512i) {
    unsafe {
        let x_hi = _mm512_castps_si512(_mm512_movehdup_ps(_mm512_castsi512_ps(x)));
        let y_hi = _mm512_castps_si512(_mm512_movehdup_ps(_mm512_castsi512_ps(y)));

        let mul_ll = _mm512_mul_epu32(x, y);
        let mul_lh = _mm512_mul_epu32(x, y_hi);
        let mul_hl = _mm512_mul_epu32(x_hi, y);
        let mul_hh = _mm512_mul_epu32(x_hi, y_hi);

        let mul_ll_hi = _mm512_srli_epi64::<32>(mul_ll);
        let t0 = _mm512_add_epi64(mul_hl, mul_ll_hi);
        let t0_lo = _mm512_and_si512(t0, EPSILON);
        let t0_hi = _mm512_srli_epi64::<32>(t0);
        let t1 = _mm512_add_epi64(mul_lh, t0_lo);
        let t2 = _mm512_add_epi64(mul_hh, t0_hi);
        let t1_hi = _mm512_srli_epi64::<32>(t1);
        let res_hi = _mm512_add_epi64(t2, t1_hi);

        let t1_lo = _mm512_castps_si512(_mm512_moveldup_ps(_mm512_castsi512_ps(t1)));
        let res_lo = _mm512_mask_blend_epi32(LO_32_BITS_MASK, t1_lo, mul_ll);

        (res_hi, res_lo)
    }
}

/// Full 64-bit squaring.
#[inline]
fn square64(x: __m512i) -> (__m512i, __m512i) {
    unsafe {
        let x_hi = _mm512_castps_si512(_mm512_movehdup_ps(_mm512_castsi512_ps(x)));

        let mul_ll = _mm512_mul_epu32(x, x);
        let mul_lh = _mm512_mul_epu32(x, x_hi);
        let mul_hh = _mm512_mul_epu32(x_hi, x_hi);

        let mul_ll_hi = _mm512_srli_epi64::<33>(mul_ll);
        let t0 = _mm512_add_epi64(mul_lh, mul_ll_hi);
        let t0_hi = _mm512_srli_epi64::<31>(t0);
        let res_hi = _mm512_add_epi64(mul_hh, t0_hi);

        let mul_lh_lo = _mm512_slli_epi64::<33>(mul_lh);
        let res_lo = _mm512_add_epi64(mul_ll, mul_lh_lo);

        (res_hi, res_lo)
    }
}

/// Reduce a 128-bit value (high, low) modulo `P`. Result may be > P.
#[inline]
fn reduce128(x: (__m512i, __m512i)) -> __m512i {
    unsafe {
        let (hi0, lo0) = x;

        let hi_hi0 = _mm512_srli_epi64::<32>(hi0);

        // 2^96 = -1 mod P.
        let lo1 = sub_no_double_overflow_64_64(lo0, hi_hi0);

        // Bottom 32 bits of hi0 times 2^64 = 2^32 - 1 mod P.
        let t1 = _mm512_mul_epu32(hi0, EPSILON);

        add_no_double_overflow_64_64(lo1, t1)
    }
}

#[inline]
fn mul(x: __m512i, y: __m512i) -> __m512i {
    reduce128(mul64_64(x, y))
}

#[inline]
fn square(x: __m512i) -> __m512i {
    reduce128(square64(x))
}

// =========================================================================
// SIMD-vectorized Poseidon1 MDS multiplication
// =========================================================================
//
// Computes the width-8 circulant MDS matrix-vector product entirely in
// `__m512i` registers, with delayed reduction. Each output is
// `sum_j MDS_ROW[(j-i) mod 8] * state[j]`. Coefficients are in
// {1, 3, 4, 7, 8, 9} (max 9), so per-term products fit in u68 and sums of
// 8 terms fit comfortably in u71.
//
// We multiply via two 32x32 `_mm512_mul_epu32` calls (low half and high
// half of state), which exploits that the constants fit in 4 bits (so the
// "high 32 bits" operand of mul_epu32 is zero by construction). Sums of
// the low and high halves are accumulated separately into u64s, then we
// assemble the (hi, lo) u128 pair and call `reduce128`.

use crate::poseidon1::{MDS8_ROW, POSEIDON1_WIDTH};

/// SIMD MDS multiplication for the width-8 circulant Poseidon1 matrix.
#[inline]
pub(crate) fn mds_mul_simd(state: &mut [PackedGoldilocksAVX512; POSEIDON1_WIDTH]) {
    unsafe {
        let s: [__m512i; 8] = core::array::from_fn(|i| state[i].to_vector());
        // Precompute the high 32 bits of every state slot once.
        let s_hi: [__m512i; 8] = core::array::from_fn(|i| _mm512_srli_epi64::<32>(s[i]));

        // For each output i, accumulate the dot product. With the inner loop
        // bound by `8` and `MDS8_ROW` const, LLVM can fully unroll and fold
        // the coefficient lookups.
        let mut out: [__m512i; 8] = [_mm512_setzero_si512(); 8];

        for i in 0..8 {
            let mut sum_ll = _mm512_setzero_si512();
            let mut sum_hl = _mm512_setzero_si512();
            for j in 0..8 {
                // Row i is `MDS8_ROW` rotated right by i, i.e. coefficient for
                // `state[j]` in output `i` is `MDS8_ROW[(j + 8 - i) % 8]`.
                let c = MDS8_ROW[(j + 8 - i) % 8];
                let c_vec = _mm512_set1_epi64(c);
                sum_ll = _mm512_add_epi64(sum_ll, _mm512_mul_epu32(s[j], c_vec));
                sum_hl = _mm512_add_epi64(sum_hl, _mm512_mul_epu32(s_hi[j], c_vec));
            }

            // Total value = sum_ll + (sum_hl << 32). Compose into (hi, lo) u128.
            // sum_ll < 2^39, sum_hl < 2^39, so sum_hl >> 32 < 2^7.
            let sum_hl_shifted = _mm512_slli_epi64::<32>(sum_hl);
            let lo = _mm512_add_epi64(sum_ll, sum_hl_shifted);
            // Detect unsigned overflow: lo < sum_hl_shifted iff the add wrapped.
            let carry_mask = _mm512_cmplt_epu64_mask(lo, sum_hl_shifted);
            let hi_no_carry = _mm512_srli_epi64::<32>(sum_hl);
            let hi = _mm512_mask_add_epi64(hi_no_carry, carry_mask, hi_no_carry, _mm512_set1_epi64(1));

            out[i] = reduce128((hi, lo));
        }

        for i in 0..8 {
            state[i] = PackedGoldilocksAVX512::from_vector(out[i]);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Goldilocks, PackedGoldilocksAVX512, WIDTH};

    const SPECIAL_VALS: [Goldilocks; WIDTH] = Goldilocks::new_array([
        0xFFFF_FFFF_0000_0001,
        0xFFFF_FFFF_0000_0000,
        0xFFFF_FFFE_FFFF_FFFF,
        0xFFFF_FFFF_FFFF_FFFF,
        0x0000_0000_0000_0000,
        0x0000_0000_0000_0001,
        0x0000_0000_0000_0002,
        0x0FFF_FFFF_F000_0000,
    ]);

    #[test]
    fn pack_round_trip() {
        let p = PackedGoldilocksAVX512(SPECIAL_VALS);
        let v = p.to_vector();
        assert_eq!(PackedGoldilocksAVX512::from_vector(v).0, SPECIAL_VALS);
    }
}
