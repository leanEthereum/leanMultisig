// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use alloc::vec::Vec;
use core::arch::x86_64::{self, __m256i};
use core::iter::{Product, Sum};
use core::mem::transmute;
use core::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use field::interleave::{interleave_u32, interleave_u64, interleave_u128};
use field::op_assign_macros::{
    impl_add_assign, impl_add_base_field, impl_div_methods, impl_mul_base_field, impl_mul_methods, impl_packed_value,
    impl_rng, impl_sub_assign, impl_sub_base_field, impl_sum_prod_base_field, ring_sum,
};
use field::{
    Algebra, Field, InjectiveMonomial, PackedField, PackedFieldPow2, PackedValue, PermutationMonomial,
    PrimeCharacteristicRing, impl_packed_field_pow_2, mm256_mod_add, mm256_mod_sub,
};
use rand::Rng;
use rand::distr::{Distribution, StandardUniform};
use utils::reconstitute_from_base;

use crate::{FieldParameters, MontyField31, PackedMontyParameters, RelativelyPrimePower, halve_avx2};

const WIDTH: usize = 8;

pub trait MontyParametersAVX2 {
    const PACKED_P: __m256i;
    const PACKED_MU: __m256i;
}

/// Vectorized AVX2 implementation of `MontyField31<FP>` arithmetic.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
#[repr(transparent)] // This is needed to make `transmute`s safe.
#[must_use]
pub struct PackedMontyField31AVX2<PMP: PackedMontyParameters>(pub [MontyField31<PMP>; WIDTH]);

impl<PMP: PackedMontyParameters> PackedMontyField31AVX2<PMP> {
    #[inline]
    #[must_use]
    /// Get an arch-specific vector representing the packed values.
    pub(crate) fn to_vector(self) -> __m256i {
        unsafe {
            // Safety: `MontyField31<FP>` is `repr(transparent)` so it can be transmuted to `u32`. It
            // follows that `[MontyField31<FP>; WIDTH]` can be transmuted to `[u32; WIDTH]`, which can be
            // transmuted to `__m256i`, since arrays are guaranteed to be contiguous in memory.
            // Finally `PackedMontyField31AVX2<FP>` is `repr(transparent)` so it can be transmuted to
            // `[MontyField31<FP>; WIDTH]`.
            transmute(self)
        }
    }

    #[inline]
    /// Make a packed field vector from an arch-specific vector.
    ///
    /// SAFETY: The caller must ensure that each element of `vector` represents a valid `MontyField31<FP>`.
    /// In particular, each element of vector must be in `0..P` (canonical form).
    pub unsafe fn from_vector(vector: __m256i) -> Self {
        unsafe {
            // Safety: It is up to the user to ensure that elements of `vector` represent valid
            // `MontyField31<FP>` values. We must only reason about memory representations. `__m256i` can be
            // transmuted to `[u32; WIDTH]` (since arrays elements are contiguous in memory), which can
            // be transmuted to `[MontyField31<FP>; WIDTH]` (since `MontyField31<FP>` is `repr(transparent)`), which in
            // turn can be transmuted to `PackedMontyField31AVX2<FP>` (since `PackedMontyField31AVX2<FP>` is also
            // `repr(transparent)`).
            transmute(vector)
        }
    }

    /// Copy `value` to all positions in a packed vector. This is the same as
    /// `From<MontyField31<FP>>::from`, but `const`.
    #[inline]
    pub(crate) const fn broadcast(value: MontyField31<PMP>) -> Self {
        Self([value; WIDTH])
    }
}

impl<PMP: PackedMontyParameters> From<MontyField31<PMP>> for PackedMontyField31AVX2<PMP> {
    #[inline]
    fn from(value: MontyField31<PMP>) -> Self {
        Self::broadcast(value)
    }
}

impl<PMP: PackedMontyParameters> Add for PackedMontyField31AVX2<PMP> {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        let lhs = self.to_vector();
        let rhs = rhs.to_vector();
        let res = mm256_mod_add(lhs, rhs, PMP::PACKED_P);
        unsafe {
            // Safety: `mm256_mod_add` returns values in canonical form when given values in canonical form.
            Self::from_vector(res)
        }
    }
}

impl<PMP: PackedMontyParameters> Sub for PackedMontyField31AVX2<PMP> {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Self) -> Self {
        let lhs = self.to_vector();
        let rhs = rhs.to_vector();
        let res = mm256_mod_sub(lhs, rhs, PMP::PACKED_P);
        unsafe {
            // Safety: `mm256_mod_sub` returns values in canonical form when given values in canonical form.
            Self::from_vector(res)
        }
    }
}

impl<PMP: PackedMontyParameters> Neg for PackedMontyField31AVX2<PMP> {
    type Output = Self;
    #[inline]
    fn neg(self) -> Self {
        let val = self.to_vector();
        let res = neg::<PMP>(val);
        unsafe {
            // Safety: `neg` returns values in canonical form when given values in canonical form.
            Self::from_vector(res)
        }
    }
}

impl<PMP: PackedMontyParameters> Mul for PackedMontyField31AVX2<PMP> {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        let lhs = self.to_vector();
        let rhs = rhs.to_vector();
        let res = mul::<PMP>(lhs, rhs);
        unsafe {
            // Safety: `mul` returns values in canonical form when given values in canonical form.
            Self::from_vector(res)
        }
    }
}

impl_add_assign!(PackedMontyField31AVX2, (PackedMontyParameters, PMP));
impl_sub_assign!(PackedMontyField31AVX2, (PackedMontyParameters, PMP));
impl_mul_methods!(PackedMontyField31AVX2, (FieldParameters, FP));
ring_sum!(PackedMontyField31AVX2, (FieldParameters, FP));
impl_rng!(PackedMontyField31AVX2, (PackedMontyParameters, PMP));

impl<FP: FieldParameters> PrimeCharacteristicRing for PackedMontyField31AVX2<FP> {
    type PrimeSubfield = MontyField31<FP>;

    const ZERO: Self = Self::broadcast(MontyField31::ZERO);
    const ONE: Self = Self::broadcast(MontyField31::ONE);
    const TWO: Self = Self::broadcast(MontyField31::TWO);
    const NEG_ONE: Self = Self::broadcast(MontyField31::NEG_ONE);

    #[inline]
    fn from_prime_subfield(f: Self::PrimeSubfield) -> Self {
        f.into()
    }

    #[inline]
    fn halve(&self) -> Self {
        let val = self.to_vector();
        let halved = halve_avx2::<FP>(val);
        unsafe {
            // Safety: `halve_avx2` returns values in canonical form when given values in canonical form.
            Self::from_vector(halved)
        }
    }

    #[inline]
    fn cube(&self) -> Self {
        // The optimized `apply_func_to_even_odd` + `packed_exp_3` path keeps an
        // intermediate "signed in (-P, P)" value packed in i32 lanes. That
        // representation is unambiguous only when `P < 2^31`. The current 32-bit
        // prime (`P = 0xfa000001`) violates that, so route through the canonical
        // unsigned Mul, mirroring AVX512.
        *self * self.square()
    }

    #[inline]
    fn andn(&self, rhs: &Self) -> Self {
        let lhs = self.to_vector();
        let rhs = rhs.to_vector();
        let res = andn::<FP>(lhs, rhs);
        unsafe {
            // Safety: `andn` returns values in canonical form when given values in canonical form.
            Self::from_vector(res)
        }
    }
    // `xor` is left to the default trait implementation. The optimised
    // packed routine assumes `2*lhs` and `2^31 - rhs` fit in a u32 without
    // wrap-around, which only holds for `P < 2^31`. With the current 32-bit
    // prime the wrap can push `lhs * rhs` past `2^32 * P` and break the
    // Montgomery reduction.

    // The `packed_exp_*` helpers (`apply_func_to_even_odd` + signed Montgomery)
    // assume `P < 2^31`. With the current 32-bit prime they would overflow, so we
    // fall back to the default `exp_const_u64` implementation, which composes
    // canonical `square` / `cube` calls. Mirrors AVX512.

    #[inline(always)]
    fn dot_product<const N: usize>(u: &[Self; N], v: &[Self; N]) -> Self {
        general_dot_product::<_, _, _, N>(u, v)
    }

    #[inline(always)]
    fn zero_vec(len: usize) -> Vec<Self> {
        // SAFETY: this is a repr(transparent) wrapper around an array.
        unsafe { reconstitute_from_base(MontyField31::<FP>::zero_vec(len * WIDTH)) }
    }
}

impl_add_base_field!(PackedMontyField31AVX2, MontyField31, (PackedMontyParameters, PMP));
impl_sub_base_field!(PackedMontyField31AVX2, MontyField31, (PackedMontyParameters, PMP));
impl_mul_base_field!(PackedMontyField31AVX2, MontyField31, (PackedMontyParameters, PMP));
impl_div_methods!(PackedMontyField31AVX2, MontyField31, (FieldParameters, FP));
impl_sum_prod_base_field!(PackedMontyField31AVX2, MontyField31, (FieldParameters, FP));

impl<FP: FieldParameters> Algebra<MontyField31<FP>> for PackedMontyField31AVX2<FP> {}

// MONTGOMERY MULTIPLICATION
//   This implementation is based on [1] but with minor changes. The reduction is as follows:
//
// Constants: P < 2^31, prime
//            B = 2^32
//            μ = P^-1 mod B
// Input: 0 <= C < P B
// Output: 0 <= R < P such that R = C B^-1 (mod P)
//   1. Q := μ C mod B
//   2. D := (C - Q P) / B
//   3. R := if D < 0 then D + P else D
//
// We first show that the division in step 2. is exact. It suffices to show that C = Q P (mod B). By
// definition of Q and μ, we have Q P = μ C P = P^-1 C P = C (mod B). We also have
// C - Q P = C (mod P), so thus D = C B^-1 (mod P).
//
// It remains to show that R is in the correct range. It suffices to show that -P < D < P. We know
// that 0 <= C < P B and 0 <= Q P < P B. Then -P B < C - QP < P B and -P < D < P, as desired.
//
// [1] Modern Computer Arithmetic, Richard Brent and Paul Zimmermann, Cambridge University Press,
//     2010, algorithm 2.7.

// We provide 2 variants of Montgomery reduction depending on if the inputs are unsigned or signed.
// The unsigned variant follows steps 1 and 2 in the above protocol to produce D in (-P, ..., P).
// For the signed variant we assume -PB/2 < C < PB/2 and let Q := μ C mod B be the unique
// representative in [-B/2, ..., B/2 - 1]. The division in step 2 is clearly still exact and
// |C - Q P| <= |C| + |Q||P| < PB so D still lies in (-P, ..., P).

/// Perform a partial Montgomery reduction on each 64 bit element, producing a canonical result.
///
/// Input must lie in `{0, ..., 2^32 * P}` (per 64-bit lane).
/// The output is canonical (`[0, P)`) and stored in the upper 32 bits of each 64-bit lane.
///
/// For `P < 2^32` (including `P > 2^31`) we cannot represent the partial reduction
/// "signed in (-P, P)" inside an `i32`, so we canonicalize directly: detect the
/// underflow `top32(input) < top32(q_p)` (unsigned compare) and conditionally add `P`.
#[inline]
#[must_use]
fn partial_monty_red_unsigned_to_canonical<MPAVX2: MontyParametersAVX2>(input: __m256i) -> __m256i {
    unsafe {
        let q = x86_64::_mm256_mul_epu32(input, MPAVX2::PACKED_MU);
        let q_p = x86_64::_mm256_mul_epu32(q, MPAVX2::PACKED_P);

        // `_mm256_sub_epi32` is fine here: the low 32 bits of `input` and `q_p` cancel by
        // construction, so the result of this 32-bit subtraction at the upper-32-bit
        // positions equals `top32(input) - top32(q_p)` (mod 2^32).
        let raw = x86_64::_mm256_sub_epi32(input, q_p);

        // Detect underflow: `top32(input) < top32(q_p)` as unsigned.
        // AVX2 has no native unsigned compare; emulate via `xor i32::MIN` + signed cmpgt.
        let flip = x86_64::_mm256_set1_epi32(i32::MIN);
        let input_f = x86_64::_mm256_xor_si256(input, flip);
        let q_p_f = x86_64::_mm256_xor_si256(q_p, flip);
        let underflow = x86_64::_mm256_cmpgt_epi32(q_p_f, input_f);
        let corr = x86_64::_mm256_and_si256(underflow, MPAVX2::PACKED_P);

        // The mask was computed at the upper-32-bit positions of each 64-bit lane (where
        // the actual subtraction result lives); the lower-32-bit values of `corr` happen
        // to have the same mask but the lower-32-bit positions of `raw` are discarded by
        // `blend_evn_odd`/`movehdup` callers anyway.
        x86_64::_mm256_add_epi32(raw, corr)
    }
}

/// Blend together in two vectors interleaving the 32-bit elements stored in the odd components.
///
/// This ignores whatever is stored in even positions.
#[inline(always)]
#[must_use]
fn blend_evn_odd(evn: __m256i, odd: __m256i) -> __m256i {
    // We want this to compile to:
    //      vmovshdup  evn_hi, evn
    //      vpblendd   t, evn_hi, odd, aah
    // throughput: 0.67 cyc/vec (12 els/cyc)
    // latency: 2 cyc
    unsafe {
        // We start with:
        //   evn = [ e0  e1  e2  e3  e4  e5  e6  e7 ],
        //   odd = [ o0  o1  o2  o3  o4  o5  o6  o7 ].
        let evn_hi = movehdup_epi32(evn);
        x86_64::_mm256_blend_epi32::<0b10101010>(evn_hi, odd)
        // res = [e1, o1, e3, o3, e5, o5, e7, o7]
    }
}

/// Multiply the MontyField31 field elements in the even index entries.
/// lhs[2i], rhs[2i] must be unsigned 32-bit integers such that
/// lhs[2i] * rhs[2i] lies in {0, ..., 2^32P}.
/// The output is canonical ([0, P)) and stored in output[2i + 1].
#[inline]
#[must_use]
fn monty_mul<MPAVX2: MontyParametersAVX2>(lhs: __m256i, rhs: __m256i) -> __m256i {
    unsafe {
        let prod = x86_64::_mm256_mul_epu32(lhs, rhs);
        partial_monty_red_unsigned_to_canonical::<MPAVX2>(prod)
    }
}

#[inline]
#[must_use]
fn movehdup_epi32(x: __m256i) -> __m256i {
    // This instruction is only available in the floating-point flavor; this distinction is only for
    // historical reasons and no longer matters. We cast to floats, duplicate, and cast back.
    unsafe { x86_64::_mm256_castps_si256(x86_64::_mm256_movehdup_ps(x86_64::_mm256_castsi256_ps(x))) }
}

/// Multiply unsigned vectors of field elements returning a vector of canonical results in [0, P).
///
/// Inputs are allowed to not be in canonical form however they must obey the bound `lhs*rhs < 2^32P`. If this bound
/// is broken, the output is undefined.
#[inline]
#[must_use]
fn mul<MPAVX2: MontyParametersAVX2>(lhs: __m256i, rhs: __m256i) -> __m256i {
    // We want this to compile to:
    //      vmovshdup  lhs_odd, lhs
    //      vmovshdup  rhs_odd, rhs
    //      vpmuludq   prod_evn, lhs, rhs
    //      vpmuludq   prod_odd, lhs_odd, rhs_odd
    //      vpmuludq   q_evn, prod_evn, MU
    //      vpmuludq   q_odd, prod_odd, MU
    //      vpmuludq   q_P_evn, q_evn, P
    //      vpmuludq   q_P_odd, q_odd, P
    //      vpsubq     d_evn, prod_evn, q_P_evn
    //      vpsubq     d_odd, prod_odd, q_P_odd
    //      vmovshdup  d_evn_hi, d_evn
    //      vpblendd   t, d_evn_hi, d_odd, aah
    // throughput: 4 cyc/vec (2 els/cyc)
    // latency: 19 cyc
    let lhs_evn = lhs;
    let rhs_evn = rhs;
    let lhs_odd = movehdup_epi32(lhs);
    let rhs_odd = movehdup_epi32(rhs);

    let d_evn = monty_mul::<MPAVX2>(lhs_evn, rhs_evn);
    let d_odd = monty_mul::<MPAVX2>(lhs_odd, rhs_odd);

    blend_evn_odd(d_evn, d_odd)
}

/// Lets us combine some code for MontyField31<FP> and PackedMontyField31AVX2<FP> elements.
///
/// Provides methods to convert an element into a __m256i element and then shift this __m256i
/// element so that the odd elements now lie in the even positions. Depending on the type of input,
/// the shift might be a no-op.
trait IntoM256<PMP: PackedMontyParameters>: Copy + Into<PackedMontyField31AVX2<PMP>> {
    /// Convert the input into a __m256i element.
    fn as_m256i(&self) -> __m256i;

    /// Convert the input to a __m256i element and shift so that all elements in odd positions
    /// now lie in even positions.
    ///
    /// The values lying in the even positions are undefined.
    #[inline(always)]
    fn as_shifted_m256i(&self) -> __m256i {
        let vec = self.as_m256i();
        movehdup_epi32(vec)
    }
}

impl<PMP: PackedMontyParameters> IntoM256<PMP> for PackedMontyField31AVX2<PMP> {
    #[inline(always)]
    fn as_m256i(&self) -> __m256i {
        self.to_vector()
    }
}

impl<PMP: PackedMontyParameters> IntoM256<PMP> for MontyField31<PMP> {
    #[inline(always)]
    fn as_m256i(&self) -> __m256i {
        unsafe { x86_64::_mm256_set1_epi32(self.value as i32) }
    }

    #[inline(always)]
    fn as_shifted_m256i(&self) -> __m256i {
        unsafe { x86_64::_mm256_set1_epi32(self.value as i32) }
    }
}

// `dot_product_2` and `dot_product_4` were specialised batched-Montgomery dot products that
// accumulated two or four 64-bit products into a single u64 before reduction. That bound only
// holds for `P < 2^31`. With the current 32-bit prime (`0xfa000001`) two products already
// overflow u64, so the helpers have been removed. `general_dot_product` accumulates each
// product through the canonical-returning `Mul` instead.

/// A general fast dot product implementation.
#[inline(always)]
fn general_dot_product<FP: FieldParameters, LHS: IntoM256<FP>, RHS: IntoM256<FP>, const N: usize>(
    lhs: &[LHS],
    rhs: &[RHS],
) -> PackedMontyField31AVX2<FP> {
    assert_eq!(lhs.len(), N);
    assert_eq!(rhs.len(), N);
    if N == 0 {
        return PackedMontyField31AVX2::<FP>::ZERO;
    }
    let mut acc: PackedMontyField31AVX2<FP> = lhs[0].into() * rhs[0].into();
    for i in 1..N {
        acc += lhs[i].into() * rhs[i].into();
    }
    acc
}

/// Compute the elementary arithmetic generalization of `andnot`, namely `andn(l, r) = (1 - l)r` of
/// vectors in canonical form.
///
/// Inputs are assumed to be in canonical form, if the inputs are not in canonical form, the result is undefined.
#[inline]
#[must_use]
fn andn<MPAVX2: MontyParametersAVX2>(lhs: __m256i, rhs: __m256i) -> __m256i {
    // As we are working with MONTY_CONSTANT = 2^32, the internal representation
    // of 1 is 2^32 mod P = 2^32 - P mod P. Hence we compute (2^32 - P - l)r.
    // This product is less than 2^32P so we can apply our monty reduction to this.
    //
    // We want this to compile to:
    //      vpsubd     neg_lhs, -P, lhs
    //      vmovshdup  lhs_odd, neg_lhs
    //      vmovshdup  rhs_odd, rhs
    //      vpmuludq   prod_evn, neg_lhs, rhs
    //      vpmuludq   prod_odd, lhs_odd, rhs_odd
    //      vpmuludq   q_evn, prod_evn, MU
    //      vpmuludq   q_odd, prod_odd, MU
    //      vpmuludq   q_P_evn, q_evn, P
    //      vpmuludq   q_P_odd, q_odd, P
    //      vpsubq     d_evn, prod_evn, q_P_evn
    //      vpsubq     d_odd, prod_odd, q_P_odd
    //      vmovshdup  d_evn_hi, d_evn
    //      vpblendd   t, d_evn_hi, d_odd, aah
    //      vpaddd     corr, t, P
    //      vpminud    res, t, corr
    // throughput: 5 cyc/vec (1.6 els/cyc)
    // latency: 20 cyc
    unsafe {
        // M(1) = 2^32 mod P = 2^32 - P (since P < 2^32). We need
        // `neg_lhs = M(1) - lhs (mod P)`, i.e. a canonical value in [0, P).
        //
        // For P < 2^31 the simple `(2^32 - P) - lhs` computed mod 2^32 is
        // already in [0, M(1)] ⊂ [0, P) because lhs < P < M(1). For P > 2^31,
        // M(1) = 2^32 - P < P, so `lhs` may exceed M(1) and the subtraction
        // wraps mod 2^32, producing a value in [M(1)+1, 2^32) that is no
        // longer congruent to `M(1) - lhs` mod P (it differs by `2^32 mod P`).
        //
        // Use `mm256_mod_sub` to do the subtraction correctly mod P for any
        // `P < 2^32`.
        let one_monty = x86_64::_mm256_sub_epi32(x86_64::_mm256_setzero_si256(), MPAVX2::PACKED_P);
        let neg_lhs = mm256_mod_sub(one_monty, lhs, MPAVX2::PACKED_P);

        // `neg_lhs` is canonical in [0, P), so `neg_lhs * rhs < 2^32 * P` and
        // we can apply the standard Montgomery reduction. `mul` returns a
        // canonical result.
        mul::<MPAVX2>(neg_lhs, rhs)
    }
}

// `packed_exp_*`, `apply_func_to_even_odd`, `monty_mul_signed`,
// `partial_monty_red_signed_to_signed`, `shifted_square`, and
// `red_signed_to_canonical` were used to implement the optimised cube /
// exp_5 / exp_7 paths. They all relied on a "signed in `(-P, P)` stored as
// i32" intermediate representation, which is unambiguous only when
// `P < 2^31`. With the current 32-bit prime they were producing wrong
// results, so the optimised paths have been removed and `cube` /
// `exp_const_u64` now go through the canonical-returning `Mul` directly.

/// Negate a vector of MontyField31 field elements in canonical form.
/// If the inputs are not in canonical form, the result is undefined.
#[inline]
#[must_use]
fn neg<MPAVX2: MontyParametersAVX2>(val: __m256i) -> __m256i {
    // We want to return `(P - val) mod P`, i.e. `0` if `val == 0` else `P - val`.
    //
    // The previous implementation used `vpsignd(P - val, val)`, which exploits the
    // fact that `val` is non-negative as a signed i32 when `P < 2^31`. With the
    // current 32-bit prime (`P > 2^31`) `val` can have its sign bit set and
    // `vpsignd` would return `-(P - val)` instead of `(P - val)`. So we use a
    // mask-based approach that works for any `P < 2^32`.
    unsafe {
        // Safety: If this code got compiled then AVX2 intrinsics are available.
        let t = x86_64::_mm256_sub_epi32(MPAVX2::PACKED_P, val);
        let zero = x86_64::_mm256_setzero_si256();
        let is_zero = x86_64::_mm256_cmpeq_epi32(val, zero);
        // `andnot(is_zero, t)` = `(!is_zero) & t` = `t` when `val != 0`, else `0`.
        x86_64::_mm256_andnot_si256(is_zero, t)
    }
}

impl<FP: FieldParameters + RelativelyPrimePower<D>, const D: u64> InjectiveMonomial<D> for PackedMontyField31AVX2<FP> {}

impl<FP: FieldParameters + RelativelyPrimePower<D>, const D: u64> PermutationMonomial<D>
    for PackedMontyField31AVX2<FP>
{
    fn injective_exp_root_n(&self) -> Self {
        FP::exp_root_d(*self)
    }
}

impl_packed_value!(
    PackedMontyField31AVX2,
    MontyField31,
    WIDTH,
    (PackedMontyParameters, PMP)
);

unsafe impl<FP: FieldParameters> PackedField for PackedMontyField31AVX2<FP> {
    type Scalar = MontyField31<FP>;

    #[inline]
    fn packed_linear_combination<const N: usize>(coeffs: &[Self::Scalar], vecs: &[Self]) -> Self {
        general_dot_product::<_, _, _, N>(coeffs, vecs)
    }
}

impl_packed_field_pow_2!(
    PackedMontyField31AVX2, (FieldParameters, FP);
    [
        (1, interleave_u32),
        (2, interleave_u64),
        (4, interleave_u128)
    ],
    WIDTH
);

/// Multiplication by a base field element in a binomial extension field.
#[inline]
pub fn base_mul_packed<FP, const WIDTH: usize>(
    a: [MontyField31<FP>; WIDTH],
    b: MontyField31<FP>,
    res: &mut [MontyField31<FP>; WIDTH],
) where
    FP: FieldParameters,
{
    match WIDTH {
        1 => res[0] = a[0] * b,
        4 => {
            let zero = MontyField31::<FP>::ZERO;
            let lhs = PackedMontyField31AVX2([a[0], a[1], a[2], a[3], zero, zero, zero, zero]);

            let out = lhs * b;

            res.copy_from_slice(&out.0[..4]);
        }
        5 => {
            let zero = MontyField31::<FP>::ZERO;
            let lhs = PackedMontyField31AVX2([a[0], a[1], a[2], a[3], zero, zero, zero, zero]);

            let out = lhs * b;
            res[4] = a[4] * b;

            res[..4].copy_from_slice(&out.0[..4]);
        }
        8 => {
            let lhs = PackedMontyField31AVX2([a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7]]);

            let out = lhs * b;

            res.copy_from_slice(&out.0);
        }
        _ => panic!("Unsupported binomial extension degree: {}", WIDTH),
    }
}
