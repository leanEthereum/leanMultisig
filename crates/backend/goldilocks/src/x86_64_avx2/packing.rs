// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use alloc::vec::Vec;
use core::arch::x86_64::*;
use core::fmt::Debug;
use core::iter::{Product, Sum};
use core::mem::transmute;
use core::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use field::interleave::{interleave_u64, interleave_u128};
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

const WIDTH: usize = 4;

/// Vectorized AVX2 implementation of `Goldilocks` arithmetic.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
#[repr(transparent)] // Needed to make `transmute`s safe.
#[must_use]
pub struct PackedGoldilocksAVX2(pub [Goldilocks; WIDTH]);

impl PackedGoldilocksAVX2 {
    /// Get an arch-specific vector representing the packed values.
    #[inline]
    #[must_use]
    pub(crate) fn to_vector(self) -> __m256i {
        unsafe {
            // Safety: `Goldilocks` is `repr(transparent)` over `u64`, so
            // `[Goldilocks; 4]` and `__m256i` share size and layout.
            transmute(self)
        }
    }

    /// Make a packed field vector from an arch-specific vector.
    ///
    /// Elements of `Goldilocks` are allowed to be arbitrary u64s so this function
    /// is safe (unlike Mersenne31/MontyField31 variants).
    #[inline]
    pub(crate) fn from_vector(vector: __m256i) -> Self {
        unsafe { transmute(vector) }
    }

    /// Copy `value` to all positions in a packed vector. This is the same as
    /// `From<Goldilocks>::from`, but `const`.
    #[inline]
    const fn broadcast(value: Goldilocks) -> Self {
        Self([value; WIDTH])
    }
}

impl From<Goldilocks> for PackedGoldilocksAVX2 {
    fn from(x: Goldilocks) -> Self {
        Self::broadcast(x)
    }
}

impl Add for PackedGoldilocksAVX2 {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        Self::from_vector(add(self.to_vector(), rhs.to_vector()))
    }
}

impl Sub for PackedGoldilocksAVX2 {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Self) -> Self {
        Self::from_vector(sub(self.to_vector(), rhs.to_vector()))
    }
}

impl Neg for PackedGoldilocksAVX2 {
    type Output = Self;
    #[inline]
    fn neg(self) -> Self {
        Self::from_vector(neg(self.to_vector()))
    }
}

impl Mul for PackedGoldilocksAVX2 {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        Self::from_vector(mul(self.to_vector(), rhs.to_vector()))
    }
}

impl_add_assign!(PackedGoldilocksAVX2);
impl_sub_assign!(PackedGoldilocksAVX2);
impl_mul_methods!(PackedGoldilocksAVX2);
ring_sum!(PackedGoldilocksAVX2);
impl_rng!(PackedGoldilocksAVX2);

impl PrimeCharacteristicRing for PackedGoldilocksAVX2 {
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

// Goldilocks: p - 1 = 2^32 * 3 * 5 * 17 * ...; smallest D coprime to (p-1) is 7.
impl InjectiveMonomial<7> for PackedGoldilocksAVX2 {}

impl PermutationMonomial<7> for PackedGoldilocksAVX2 {
    fn injective_exp_root_n(&self) -> Self {
        exp_10540996611094048183(*self)
    }
}

impl_add_base_field!(PackedGoldilocksAVX2, Goldilocks);
impl_sub_base_field!(PackedGoldilocksAVX2, Goldilocks);
impl_mul_base_field!(PackedGoldilocksAVX2, Goldilocks);
impl_div_methods!(PackedGoldilocksAVX2, Goldilocks);
impl_sum_prod_base_field!(PackedGoldilocksAVX2, Goldilocks);

impl Algebra<Goldilocks> for PackedGoldilocksAVX2 {}

impl_packed_value!(PackedGoldilocksAVX2, Goldilocks, WIDTH);

unsafe impl PackedField for PackedGoldilocksAVX2 {
    type Scalar = Goldilocks;
}

impl_packed_field_pow_2!(
    PackedGoldilocksAVX2;
    [
        (1, interleave_u64),
        (2, interleave_u128),
    ],
    WIDTH
);

// Resources:
// 1. Intel Intrinsics Guide: https://software.intel.com/sites/landingpage/IntrinsicsGuide/
// 2. uops.info: https://uops.info/table.html
//
// Implementation notes:
// - AVX has no unsigned 64-bit comparisons. We emulate them via signed comparisons after a
//   1<<63 shift (`shift`/`canonicalize_s`/etc).
// - AVX has no add-with-carry; emulated via `result < operand` overflow detection.

const SIGN_BIT: __m256i = unsafe { transmute([i64::MIN; WIDTH]) };
const SHIFTED_FIELD_ORDER: __m256i = unsafe { transmute([Goldilocks::ORDER_U64 ^ (i64::MIN as u64); WIDTH]) };

/// Equal to `2^32 - 1 = 2^64 mod P`.
const EPSILON: __m256i = unsafe { transmute([Goldilocks::ORDER_U64.wrapping_neg(); WIDTH]) };

/// Add 2^63 (XOR with sign bit). Used to emulate unsigned compares with signed ones.
#[inline]
fn shift(x: __m256i) -> __m256i {
    unsafe { _mm256_xor_si256(x, SIGN_BIT) }
}

/// Convert to canonical representation. Argument is shifted by 1<<63; result is too.
#[inline]
unsafe fn canonicalize_s(x_s: __m256i) -> __m256i {
    unsafe {
        let mask = _mm256_cmpgt_epi64(SHIFTED_FIELD_ORDER, x_s);
        let wrapback_amt = _mm256_andnot_si256(mask, EPSILON);
        _mm256_add_epi64(x_s, wrapback_amt)
    }
}

/// Add `x + y_s` where `y_s` is pre-shifted; output is shifted. Assumes `x + y < 2^64 + P`.
#[inline]
unsafe fn add_no_double_overflow_64_64s_s(x: __m256i, y_s: __m256i) -> __m256i {
    unsafe {
        let res_wrapped_s = _mm256_add_epi64(x, y_s);
        let mask = _mm256_cmpgt_epi64(y_s, res_wrapped_s);
        let wrapback_amt = _mm256_srli_epi64::<32>(mask);
        _mm256_add_epi64(res_wrapped_s, wrapback_amt)
    }
}

/// Goldilocks modular addition. Result may exceed `P`.
#[inline]
fn add(x: __m256i, y: __m256i) -> __m256i {
    unsafe {
        let y_s = shift(y);
        let res_s = add_no_double_overflow_64_64s_s(x, canonicalize_s(y_s));
        shift(res_s)
    }
}

/// Goldilocks modular subtraction. Result may exceed `P`.
#[inline]
fn sub(x: __m256i, y: __m256i) -> __m256i {
    unsafe {
        let mut y_s = shift(y);
        y_s = canonicalize_s(y_s);
        let x_s = shift(x);
        let mask = _mm256_cmpgt_epi64(y_s, x_s);
        let wrapback_amt = _mm256_srli_epi64::<32>(mask);
        let res_wrapped = _mm256_sub_epi64(x_s, y_s);
        _mm256_sub_epi64(res_wrapped, wrapback_amt)
    }
}

/// Goldilocks modular negation. Result may exceed `P`.
#[inline]
fn neg(y: __m256i) -> __m256i {
    unsafe {
        let y_s = shift(y);
        _mm256_sub_epi64(SHIFTED_FIELD_ORDER, canonicalize_s(y_s))
    }
}

/// Halve a vector of Goldilocks field elements.
#[inline(always)]
pub(crate) fn halve(input: __m256i) -> __m256i {
    // For val in [0, P): val even -> val/2 = val>>1; val odd -> (val+P)/2 = (val>>1) + (P+1)/2.
    unsafe {
        const ONE: __m256i = unsafe { transmute([1_i64; 4]) };
        const ZERO: __m256i = unsafe { transmute([0_i64; 4]) };
        let half = _mm256_set1_epi64x(P.div_ceil(2) as i64);

        let least_bit = _mm256_and_si256(input, ONE);
        let t = _mm256_srli_epi64::<1>(input);
        let neg_least_bit = _mm256_sub_epi64(ZERO, least_bit);
        let maybe_half = _mm256_and_si256(half, neg_least_bit);
        _mm256_add_epi64(t, maybe_half)
    }
}

/// Full 64x64 -> 128 multiplication, returning `(hi, lo)`.
#[inline]
fn mul64_64(x: __m256i, y: __m256i) -> (__m256i, __m256i) {
    unsafe {
        // Move the high 32 bits of each lane into the low 32 bits via a float-domain swizzle.
        // (vpshufd / movehdup runs on port 5 and doesn't compete with the multiplier on ports 0/1.)
        let x_hi = _mm256_castps_si256(_mm256_movehdup_ps(_mm256_castsi256_ps(x)));
        let y_hi = _mm256_castps_si256(_mm256_movehdup_ps(_mm256_castsi256_ps(y)));

        let mul_ll = _mm256_mul_epu32(x, y);
        let mul_lh = _mm256_mul_epu32(x, y_hi);
        let mul_hl = _mm256_mul_epu32(x_hi, y);
        let mul_hh = _mm256_mul_epu32(x_hi, y_hi);

        let mul_ll_hi = _mm256_srli_epi64::<32>(mul_ll);
        let t0 = _mm256_add_epi64(mul_hl, mul_ll_hi);
        let t0_lo = _mm256_and_si256(t0, EPSILON);
        let t0_hi = _mm256_srli_epi64::<32>(t0);
        let t1 = _mm256_add_epi64(mul_lh, t0_lo);
        let t2 = _mm256_add_epi64(mul_hh, t0_hi);
        let t1_hi = _mm256_srli_epi64::<32>(t1);
        let res_hi = _mm256_add_epi64(t2, t1_hi);

        let t1_lo = _mm256_castps_si256(_mm256_moveldup_ps(_mm256_castsi256_ps(t1)));
        let res_lo = _mm256_blend_epi32::<0xaa>(mul_ll, t1_lo);

        (res_hi, res_lo)
    }
}

/// Full 64-bit squaring.
#[inline]
fn square64(x: __m256i) -> (__m256i, __m256i) {
    unsafe {
        let x_hi = _mm256_castps_si256(_mm256_movehdup_ps(_mm256_castsi256_ps(x)));

        let mul_ll = _mm256_mul_epu32(x, x);
        let mul_lh = _mm256_mul_epu32(x, x_hi);
        let mul_hh = _mm256_mul_epu32(x_hi, x_hi);

        let mul_ll_hi = _mm256_srli_epi64::<33>(mul_ll);
        let t0 = _mm256_add_epi64(mul_lh, mul_ll_hi);
        let t0_hi = _mm256_srli_epi64::<31>(t0);
        let res_hi = _mm256_add_epi64(mul_hh, t0_hi);

        let mul_lh_lo = _mm256_slli_epi64::<33>(mul_lh);
        let res_lo = _mm256_add_epi64(mul_ll, mul_lh_lo);

        (res_hi, res_lo)
    }
}

/// Add `x_s + y` where `x_s` is pre-shifted by 2^63 and `y <= 2^64 - 2^32`. Result is shifted.
#[inline]
unsafe fn add_small_64s_64_s(x_s: __m256i, y: __m256i) -> __m256i {
    unsafe {
        let res_wrapped_s = _mm256_add_epi64(x_s, y);
        let mask = _mm256_cmpgt_epi32(x_s, res_wrapped_s);
        let wrapback_amt = _mm256_srli_epi64::<32>(mask);
        _mm256_add_epi64(res_wrapped_s, wrapback_amt)
    }
}

/// Subtract `y` from `x_s` (`x_s` pre-shifted, `y <= 2^64 - 2^32`). Result is shifted.
#[inline]
unsafe fn sub_small_64s_64_s(x_s: __m256i, y: __m256i) -> __m256i {
    unsafe {
        let res_wrapped_s = _mm256_sub_epi64(x_s, y);
        let mask = _mm256_cmpgt_epi32(res_wrapped_s, x_s);
        let wrapback_amt = _mm256_srli_epi64::<32>(mask);
        _mm256_sub_epi64(res_wrapped_s, wrapback_amt)
    }
}

/// Reduce a 128-bit value (high, low) modulo `P`. Result may exceed `P`.
#[inline]
fn reduce128(x: (__m256i, __m256i)) -> __m256i {
    unsafe {
        let (hi0, lo0) = x;

        let lo0_s = shift(lo0);

        let hi_hi0 = _mm256_srli_epi64::<32>(hi0);

        // 2^96 = -1 mod P.
        let lo1_s = sub_small_64s_64_s(lo0_s, hi_hi0);

        // Bottom 32 bits of hi0 times 2^64 = 2^32 - 1 = EPSILON mod P.
        let t1 = _mm256_mul_epu32(hi0, EPSILON);

        let lo2_s = add_small_64s_64_s(lo1_s, t1);
        shift(lo2_s)
    }
}

/// Goldilocks modular multiplication. Result may exceed `P`.
#[inline]
fn mul(x: __m256i, y: __m256i) -> __m256i {
    reduce128(mul64_64(x, y))
}

/// Goldilocks modular square. Result may exceed `P`.
#[inline]
fn square(x: __m256i) -> __m256i {
    reduce128(square64(x))
}

// =========================================================================
// SIMD-vectorized Poseidon1 MDS multiplication
// =========================================================================
//
// Computes the width-8 circulant MDS matrix-vector product entirely in
// `__m256i` registers, with delayed reduction. Each output is
// `sum_j MDS_ROW[(j-i) mod 8] * state[j]`. The MDS coefficients are signed
// powers of two in {-4, -2, 1, 2, 4, 8}, so each `c * x` is implemented as a
// `vpsllq` (1-cycle latency) followed by a `vpaddq`/`vpsubq` — strictly
// faster than a 32x32 `vpmuludq` (5-cycle latency) used by the original
// dense-coefficient path.
//
// We split each state element into its low/high 32-bit halves and accumulate
// `c * lo` and `c * hi` separately into `sum_ll` and `sum_hl`. The two
// accumulators are pre-biased so positive contributions add and negative
// ones subtract without underflowing the unsigned u64 lanes; the biases also
// encode an exact `8 * P` offset, so the composed u128 stays non-negative
// AND the modular result is unchanged.

use crate::poseidon1::{MDS8_ROW, POSEIDON1_WIDTH};

// BIAS_LL + BIAS_HL << 32 = 8 * P. With sum_signed in [-6*(2^64-1), 17*(2^64-1)],
// the composed u128 = 8*P + sum_signed >= 2*P > 0. Each bias also exceeds the
// largest negative partial-sum (6 * (2^32 - 1) ≈ 2^34.6) so no lane ever
// underflows during accumulation regardless of iteration order.
const MDS_BIAS_LL: i64 = 0x0000_0007_0000_0008;
const MDS_BIAS_HL: i64 = 0x0000_0007_FFFF_FFF1;

/// `acc + (x << SHIFT)` as 64-bit lanes, with `SHIFT == 0` collapsing to a
/// plain add (no useless shift instruction).
#[inline(always)]
unsafe fn add_shl<const SHIFT: i32>(acc: __m256i, x: __m256i) -> __m256i {
    unsafe {
        if SHIFT == 0 {
            _mm256_add_epi64(acc, x)
        } else {
            _mm256_add_epi64(acc, _mm256_slli_epi64::<SHIFT>(x))
        }
    }
}

/// `acc - (x << SHIFT)`.
#[inline(always)]
unsafe fn sub_shl<const SHIFT: i32>(acc: __m256i, x: __m256i) -> __m256i {
    unsafe {
        if SHIFT == 0 {
            _mm256_sub_epi64(acc, x)
        } else {
            _mm256_sub_epi64(acc, _mm256_slli_epi64::<SHIFT>(x))
        }
    }
}

/// Apply one MDS row coefficient `c ∈ {-4,-2,1,2,4,8}` for column `j`. The
/// const generic `C` lets each call site specialize: `c * x` collapses to a
/// shift (and sign-flipped accumulation for negative `c`).
#[inline(always)]
unsafe fn accum_term<const C: i64>(sum_ll: &mut __m256i, sum_hl: &mut __m256i, s_lo: __m256i, s_hi: __m256i) {
    unsafe {
        match C {
            1 => {
                *sum_ll = add_shl::<0>(*sum_ll, s_lo);
                *sum_hl = add_shl::<0>(*sum_hl, s_hi);
            }
            2 => {
                *sum_ll = add_shl::<1>(*sum_ll, s_lo);
                *sum_hl = add_shl::<1>(*sum_hl, s_hi);
            }
            4 => {
                *sum_ll = add_shl::<2>(*sum_ll, s_lo);
                *sum_hl = add_shl::<2>(*sum_hl, s_hi);
            }
            8 => {
                *sum_ll = add_shl::<3>(*sum_ll, s_lo);
                *sum_hl = add_shl::<3>(*sum_hl, s_hi);
            }
            -2 => {
                *sum_ll = sub_shl::<1>(*sum_ll, s_lo);
                *sum_hl = sub_shl::<1>(*sum_hl, s_hi);
            }
            -4 => {
                *sum_ll = sub_shl::<2>(*sum_ll, s_lo);
                *sum_hl = sub_shl::<2>(*sum_hl, s_hi);
            }
            _ => panic!("unsupported MDS coefficient"),
        }
    }
}

/// Compose `(sum_hl << 32) + sum_ll` into a u128 `(hi, lo)` pair, then reduce
/// modulo `P`. Centralised so all 8 rows go through the same code path.
#[inline(always)]
unsafe fn finalize_row(sum_ll: __m256i, sum_hl: __m256i) -> __m256i {
    unsafe {
        let sum_hl_shifted = _mm256_slli_epi64::<32>(sum_hl);
        let lo = _mm256_add_epi64(sum_ll, sum_hl_shifted);
        // Detect unsigned overflow on `sum_ll + sum_hl_shifted`: AVX2 lacks a
        // native unsigned compare, so we XOR with the sign bit to fall back
        // on the signed compare (`cmpgt` after the same flip).
        let lo_s = _mm256_xor_si256(lo, SIGN_BIT);
        let sum_hl_shifted_s = _mm256_xor_si256(sum_hl_shifted, SIGN_BIT);
        let carry_mask = _mm256_cmpgt_epi64(sum_hl_shifted_s, lo_s);
        let hi_no_carry = _mm256_srli_epi64::<32>(sum_hl);
        // `carry_mask = -1` on overflow, `0` otherwise; subtracting `-1` adds 1.
        let hi = _mm256_sub_epi64(hi_no_carry, carry_mask);
        reduce128((hi, lo))
    }
}

/// Accumulate one full row `[c0..c7]` (a circular shift of `MDS8_ROW`) and
/// reduce. Each `accum_term::<Ck>` is monomorphised so the entire row reduces
/// to a straight-line sequence of shift / add / sub instructions.
#[inline(always)]
#[allow(clippy::too_many_arguments)]
unsafe fn mds_row<
    const C0: i64,
    const C1: i64,
    const C2: i64,
    const C3: i64,
    const C4: i64,
    const C5: i64,
    const C6: i64,
    const C7: i64,
>(
    s: &[__m256i; 8],
    s_hi: &[__m256i; 8],
    bias_ll: __m256i,
    bias_hl: __m256i,
) -> __m256i {
    unsafe {
        let mut sum_ll = bias_ll;
        let mut sum_hl = bias_hl;
        accum_term::<C0>(&mut sum_ll, &mut sum_hl, s[0], s_hi[0]);
        accum_term::<C1>(&mut sum_ll, &mut sum_hl, s[1], s_hi[1]);
        accum_term::<C2>(&mut sum_ll, &mut sum_hl, s[2], s_hi[2]);
        accum_term::<C3>(&mut sum_ll, &mut sum_hl, s[3], s_hi[3]);
        accum_term::<C4>(&mut sum_ll, &mut sum_hl, s[4], s_hi[4]);
        accum_term::<C5>(&mut sum_ll, &mut sum_hl, s[5], s_hi[5]);
        accum_term::<C6>(&mut sum_ll, &mut sum_hl, s[6], s_hi[6]);
        accum_term::<C7>(&mut sum_ll, &mut sum_hl, s[7], s_hi[7]);
        finalize_row(sum_ll, sum_hl)
    }
}

/// SIMD MDS multiplication for the width-8 circulant Poseidon1 matrix.
#[inline]
pub(crate) fn mds_mul_simd(state: &mut [PackedGoldilocksAVX2; POSEIDON1_WIDTH]) {
    // Sanity: the row decomposition below assumes the canonical
    // [2, -4, -2, 8, 1, 1, 4, 1] coefficient set.
    const _: () = assert!(MDS8_ROW[0] == 2);
    const _: () = assert!(MDS8_ROW[1] == -4);
    const _: () = assert!(MDS8_ROW[2] == -2);
    const _: () = assert!(MDS8_ROW[3] == 8);
    const _: () = assert!(MDS8_ROW[4] == 1);
    const _: () = assert!(MDS8_ROW[5] == 1);
    const _: () = assert!(MDS8_ROW[6] == 4);
    const _: () = assert!(MDS8_ROW[7] == 1);

    unsafe {
        let raw: [__m256i; 8] = core::array::from_fn(|i| state[i].to_vector());
        // Pre-split each 64-bit lane into its low and high 32-bit halves,
        // both occupying the low 32 bits of their respective lanes.
        // `s_lo[j] << k` then correctly produces `c * (state[j] & 2^32-1)`
        // without contamination from the upper 32 bits of state.
        let s_lo: [__m256i; 8] = core::array::from_fn(|i| _mm256_and_si256(raw[i], EPSILON));
        let s_hi: [__m256i; 8] = core::array::from_fn(|i| _mm256_srli_epi64::<32>(raw[i]));

        let bias_ll = _mm256_set1_epi64x(MDS_BIAS_LL);
        let bias_hl = _mm256_set1_epi64x(MDS_BIAS_HL);

        // Row i = MDS_ROW rotated right by i.
        let out0 = mds_row::<2, -4, -2, 8, 1, 1, 4, 1>(&s_lo, &s_hi, bias_ll, bias_hl);
        let out1 = mds_row::<1, 2, -4, -2, 8, 1, 1, 4>(&s_lo, &s_hi, bias_ll, bias_hl);
        let out2 = mds_row::<4, 1, 2, -4, -2, 8, 1, 1>(&s_lo, &s_hi, bias_ll, bias_hl);
        let out3 = mds_row::<1, 4, 1, 2, -4, -2, 8, 1>(&s_lo, &s_hi, bias_ll, bias_hl);
        let out4 = mds_row::<1, 1, 4, 1, 2, -4, -2, 8>(&s_lo, &s_hi, bias_ll, bias_hl);
        let out5 = mds_row::<8, 1, 1, 4, 1, 2, -4, -2>(&s_lo, &s_hi, bias_ll, bias_hl);
        let out6 = mds_row::<-2, 8, 1, 1, 4, 1, 2, -4>(&s_lo, &s_hi, bias_ll, bias_hl);
        let out7 = mds_row::<-4, -2, 8, 1, 1, 4, 1, 2>(&s_lo, &s_hi, bias_ll, bias_hl);

        state[0] = PackedGoldilocksAVX2::from_vector(out0);
        state[1] = PackedGoldilocksAVX2::from_vector(out1);
        state[2] = PackedGoldilocksAVX2::from_vector(out2);
        state[3] = PackedGoldilocksAVX2::from_vector(out3);
        state[4] = PackedGoldilocksAVX2::from_vector(out4);
        state[5] = PackedGoldilocksAVX2::from_vector(out5);
        state[6] = PackedGoldilocksAVX2::from_vector(out6);
        state[7] = PackedGoldilocksAVX2::from_vector(out7);
    }
}

#[cfg(test)]
mod tests {
    use super::{Goldilocks, PackedGoldilocksAVX2, WIDTH};

    const SPECIAL_VALS: [Goldilocks; WIDTH] = Goldilocks::new_array([
        0xFFFF_FFFF_0000_0000,
        0xFFFF_FFFF_FFFF_FFFF,
        0x0000_0000_0000_0001,
        0xFFFF_FFFF_0000_0001,
    ]);

    #[test]
    fn pack_round_trip() {
        let p = PackedGoldilocksAVX2(SPECIAL_VALS);
        let v = p.to_vector();
        assert_eq!(PackedGoldilocksAVX2::from_vector(v).0, SPECIAL_VALS);
    }
}
