// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

//! Optimised AVX512 implementation for packed vectors of MontyFields31 elements.
//!
//! We check that this compiles to the expected assembly code in: https://godbolt.org/z/Mz1WGYKWe

use alloc::vec::Vec;
use core::arch::asm;
use core::arch::x86_64::{self, __m256i, __m512i, __mmask8, __mmask16};
use core::hint::unreachable_unchecked;
use core::iter::{Product, Sum};
use core::mem::transmute;
use core::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use field::interleave::{interleave_u32, interleave_u64, interleave_u128, interleave_u256};
use field::op_assign_macros::{
    impl_add_assign, impl_add_base_field, impl_div_methods, impl_mul_base_field, impl_mul_methods, impl_packed_value,
    impl_rng, impl_sub_assign, impl_sub_base_field, impl_sum_prod_base_field, ring_sum,
};
use field::{
    Algebra, Field, InjectiveMonomial, PackedField, PackedFieldPow2, PackedValue, PermutationMonomial,
    PrimeCharacteristicRing, impl_packed_field_pow_2, mm512_mod_add, mm512_mod_sub,
};
use rand::Rng;
use rand::distr::{Distribution, StandardUniform};
use utils::reconstitute_from_base;

use crate::{FieldParameters, MontyField31, PackedMontyParameters, RelativelyPrimePower, halve_avx512};

const WIDTH: usize = 16;

pub trait MontyParametersAVX512 {
    const PACKED_P: __m512i;
    const PACKED_MU: __m512i;
}

const EVENS: __mmask16 = 0b0101010101010101;
const EVENS_8: __mmask8 = 0b01010101;

/// Vectorized AVX-512F implementation of `MontyField31` arithmetic.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
#[repr(transparent)] // Needed to make `transmute`s safe.
#[must_use]
pub struct PackedMontyField31AVX512<PMP: PackedMontyParameters>(pub [MontyField31<PMP>; WIDTH]);

impl<PMP: PackedMontyParameters> PackedMontyField31AVX512<PMP> {
    #[inline]
    #[must_use]
    /// Get an arch-specific vector representing the packed values.
    pub(crate) fn to_vector(self) -> __m512i {
        unsafe {
            // Safety: `MontyField31` is `repr(transparent)` so it can be transmuted to `u32`. It
            // follows that `[MontyField31; WIDTH]` can be transmuted to `[u32; WIDTH]`, which can be
            // transmuted to `__m512i`, since arrays are guaranteed to be contiguous in memory.
            // Finally `PackedMontyField31AVX512` is `repr(transparent)` so it can be transmuted to
            // `[MontyField31; WIDTH]`.
            transmute(self)
        }
    }

    #[inline]
    /// Make a packed field vector from an arch-specific vector.
    ///
    /// # Safety
    ///
    /// The caller must ensure that each element of `vector` represents a valid
    /// `MontyField31`. In particular, each element of vector must be in `0..=P`.
    pub unsafe fn from_vector(vector: __m512i) -> Self {
        unsafe {
            // Safety: It is up to the user to ensure that elements of `vector` represent valid
            // `MontyField31` values. We must only reason about memory representations. `__m512i` can be
            // transmuted to `[u32; WIDTH]` (since arrays elements are contiguous in memory), which can
            // be transmuted to `[MontyField31; WIDTH]` (since `MontyField31` is `repr(transparent)`), which
            // in turn can be transmuted to `PackedMontyField31AVX512` (since `PackedMontyField31AVX512` is also
            // `repr(transparent)`).
            transmute(vector)
        }
    }

    /// Copy `value` to all positions in a packed vector. This is the same as
    /// `From<MontyField31>::from`, but `const`.
    #[inline]
    pub(crate) const fn broadcast(value: MontyField31<PMP>) -> Self {
        Self([value; WIDTH])
    }

    /// Copy values from `arr` into the packed vector padding by zeros if necessary.
    #[inline]
    pub fn from_monty_array<const N: usize>(arr: [MontyField31<PMP>; N]) -> Self
    where
        PMP: FieldParameters,
    {
        const {
            assert!(N <= WIDTH);
        }
        let mut out = Self::ZERO;
        out.0[..N].copy_from_slice(&arr);
        out
    }
}

impl<PMP: PackedMontyParameters> From<MontyField31<PMP>> for PackedMontyField31AVX512<PMP> {
    #[inline]
    fn from(value: MontyField31<PMP>) -> Self {
        Self::broadcast(value)
    }
}

impl<PMP: PackedMontyParameters> Add for PackedMontyField31AVX512<PMP> {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        let lhs = self.to_vector();
        let rhs = rhs.to_vector();
        let res = mm512_mod_add(lhs, rhs, PMP::PACKED_P);
        unsafe {
            // Safety: `add` returns values in canonical form when given values in canonical form.
            Self::from_vector(res)
        }
    }
}

impl<PMP: PackedMontyParameters> Sub for PackedMontyField31AVX512<PMP> {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Self) -> Self {
        let lhs = self.to_vector();
        let rhs = rhs.to_vector();
        let res = mm512_mod_sub(lhs, rhs, PMP::PACKED_P);
        unsafe {
            // Safety: `mm512_mod_sub` returns values in canonical form when given values in canonical form.
            Self::from_vector(res)
        }
    }
}

impl<PMP: PackedMontyParameters> Neg for PackedMontyField31AVX512<PMP> {
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

impl<PMP: PackedMontyParameters> Mul for PackedMontyField31AVX512<PMP> {
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

impl_add_assign!(PackedMontyField31AVX512, (PackedMontyParameters, PMP));
impl_sub_assign!(PackedMontyField31AVX512, (PackedMontyParameters, PMP));
impl_mul_methods!(PackedMontyField31AVX512, (FieldParameters, FP));
ring_sum!(PackedMontyField31AVX512, (FieldParameters, FP));
impl_rng!(PackedMontyField31AVX512, (PackedMontyParameters, PMP));

impl<FP: FieldParameters> PrimeCharacteristicRing for PackedMontyField31AVX512<FP> {
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
        let halved = halve_avx512::<FP>(val);
        unsafe {
            // Safety: `halve_avx512` returns values in canonical form when given values in canonical form.
            Self::from_vector(halved)
        }
    }

    #[inline(always)]
    fn zero_vec(len: usize) -> Vec<Self> {
        // SAFETY: this is a repr(transparent) wrapper around an array.
        unsafe { reconstitute_from_base(MontyField31::<FP>::zero_vec(len * WIDTH)) }
    }

    #[inline]
    fn cube(&self) -> Self {
        // The optimized `packed_exp_3` path assumes inputs fit in [-P, P] as
        // signed 32-bit integers (i.e. P < 2^31). The current 32-bit prime
        // (P = 0xfa000001 ≈ 2^32) violates that assumption, so fall back to
        // unsigned Montgomery multiplication.
        *self * self.square()
    }

    // `xor` is left to the default trait implementation. The optimised
    // packed routine assumes `2*lhs` and `2^31 - rhs` fit in a u32 without
    // wrap-around, which only holds for `P < 2^31`. With the current 32-bit
    // prime the wrap can push `lhs * rhs` past `2^32 * P` and break the
    // Montgomery reduction.

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

    // The `packed_exp_*` helpers assume P < 2^31. With the current 32-bit
    // prime they would overflow, so we fall back to the default
    // `exp_const_u64` implementation, which composes correct `square` /
    // `cube` calls.

    #[inline(always)]
    fn dot_product<const N: usize>(u: &[Self; N], v: &[Self; N]) -> Self {
        general_dot_product::<_, _, _, N>(u, v)
    }
}

impl_add_base_field!(PackedMontyField31AVX512, MontyField31, (PackedMontyParameters, PMP));
impl_sub_base_field!(PackedMontyField31AVX512, MontyField31, (PackedMontyParameters, PMP));
impl_mul_base_field!(PackedMontyField31AVX512, MontyField31, (PackedMontyParameters, PMP));
impl_div_methods!(PackedMontyField31AVX512, MontyField31, (FieldParameters, FP));
impl_sum_prod_base_field!(PackedMontyField31AVX512, MontyField31, (FieldParameters, FP));

impl<FP: FieldParameters> Algebra<MontyField31<FP>> for PackedMontyField31AVX512<FP> {}

impl<FP: FieldParameters + RelativelyPrimePower<D>, const D: u64> InjectiveMonomial<D>
    for PackedMontyField31AVX512<FP>
{
}

impl<FP: FieldParameters + RelativelyPrimePower<D>, const D: u64> PermutationMonomial<D>
    for PackedMontyField31AVX512<FP>
{
    fn injective_exp_root_n(&self) -> Self {
        FP::exp_root_d(*self)
    }
}

/// No-op. Prevents the compiler from deducing the value of the vector.
///
/// Similar to `core::hint::black_box`, it can be used to stop the compiler applying undesirable
/// "optimizations". Unlike the built-in `black_box`, it does not force the value to be written to
/// and then read from the stack.
#[inline]
#[must_use]
fn confuse_compiler(x: __m512i) -> __m512i {
    let y;
    unsafe {
        asm!(
            "/*{0}*/",
            inlateout(zmm_reg) x => y,
            options(nomem, nostack, preserves_flags, pure),
        );
        // Below tells the compiler the semantics of this so it can still do constant folding, etc.
        // You may ask, doesn't it defeat the point of the inline asm block to tell the compiler
        // what it does? The answer is that we still inhibit the transform we want to avoid, so
        // apparently not. Idk, LLVM works in mysterious ways.
        if transmute::<__m512i, [u32; 16]>(x) != transmute::<__m512i, [u32; 16]>(y) {
            unreachable_unchecked();
        }
    }
    y
}

/// No-op. Prevents the compiler from deducing the value of the vector.
///
/// A variant of [`confuse_compiler`] for use with `__m256i` vectors.
///
/// Similar to `core::hint::black_box`, it can be used to stop the compiler applying undesirable
/// "optimizations". Unlike the built-in `black_box`, it does not force the value to be written to
/// and then read from the stack.
#[inline]
#[must_use]
fn confuse_compiler_256(x: __m256i) -> __m256i {
    let y;
    unsafe {
        asm!(
            "/*{0}*/",
            inlateout(ymm_reg) x => y,
            options(nomem, nostack, preserves_flags, pure),
        );
        // Below tells the compiler the semantics of this so it can still do constant folding, etc.
        // You may ask, doesn't it defeat the point of the inline asm block to tell the compiler
        // what it does? The answer is that we still inhibit the transform we want to avoid, so
        // apparently not. Idk, LLVM works in mysterious ways.
        if transmute::<__m256i, [u32; 8]>(x) != transmute::<__m256i, [u32; 8]>(y) {
            unreachable_unchecked();
        }
    }
    y
}

// MONTGOMERY MULTIPLICATION
//   This implementation is based on [1] but with minor changes. The reduction is as follows:
//
// Constants: P < 2^31
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
// It remains to show that R is in the correct range. It suffices to show that -P <= D < P. We know
// that 0 <= C < P B and 0 <= Q P < P B. Then -P B < C - QP < P B and -P < D < P, as desired.
//
// [1] Modern Computer Arithmetic, Richard Brent and Paul Zimmermann, Cambridge University Press,
//     2010, algorithm 2.7.

// `partial_monty_red_unsigned_to_signed` / `partial_monty_red_signed_to_signed`
// (and their consumers `shifted_square`, `packed_exp_*`, `apply_func_to_even_odd`)
// produced an intermediate "signed in (-P, P)" value stored as i32, which is
// unambiguous only when `P < 2^31`. For the current 32-bit prime they have
// been removed; `cube` / `exp_const_u64` go through canonical Mul instead.

/// Viewing the input as a vector of 16 `u32`s, copy the odd elements into the even elements below
/// them. In other words, for all `0 <= i < 8`, set the even elements according to
/// `res[2 * i] := a[2 * i + 1]`, and the odd elements according to
/// `res[2 * i + 1] := a[2 * i + 1]`.
#[inline]
#[must_use]
fn movehdup_epi32(a: __m512i) -> __m512i {
    // The instruction is only available in the floating-point flavor; this distinction is only for
    // historical reasons and no longer matters. We cast to floats, do the thing, and cast back.
    unsafe { x86_64::_mm512_castps_si512(x86_64::_mm512_movehdup_ps(x86_64::_mm512_castsi512_ps(a))) }
}

/// Viewing the input as a vector of 8 `u32`s, copy the odd elements into the even elements below
/// them. In other words, for all `0 <= i < 4`, set the even elements according to
/// `res[2 * i] := a[2 * i + 1]`, and the odd elements according to
/// `res[2 * i + 1] := a[2 * i + 1]`.
#[inline]
#[must_use]
fn movehdup_epi32_256(a: __m256i) -> __m256i {
    // The instruction is only available in the floating-point flavor; this distinction is only for
    // historical reasons and no longer matters. We cast to floats, do the thing, and cast back.
    unsafe { x86_64::_mm256_castps_si256(x86_64::_mm256_movehdup_ps(x86_64::_mm256_castsi256_ps(a))) }
}

/// Viewing `a` as a vector of 16 `u32`s, copy the odd elements into the even elements below them,
/// then merge with `src` according to the mask provided. In other words, for all `0 <= i < 8`, set
/// the even elements according to `res[2 * i] := if k[2 * i] { a[2 * i + 1] } else { src[2 * i] }`,
/// and the odd elements according to
/// `res[2 * i + 1] := if k[2 * i + 1] { a[2 * i + 1] } else { src[2 * i + 1] }`.
#[inline]
#[must_use]
fn mask_movehdup_epi32(src: __m512i, k: __mmask16, a: __m512i) -> __m512i {
    // The instruction is only available in the floating-point flavor; this distinction is only for
    // historical reasons and no longer matters.

    // While we can write this using intrinsics, when inlined, the intrinsic often compiles
    // to a vpermt2ps which has worse latency, see https://godbolt.org/z/489aaPhz3.
    // Hence we use inline assembly to force the compiler to do the right thing.
    unsafe {
        let dst: __m512i;
        asm!(
            "vmovshdup {src_dst}{{{k}}}, {a}",
            src_dst = inlateout(zmm_reg) src => dst,
            k = in(kreg) k,
            a = in(zmm_reg) a,
            options(nomem, nostack, preserves_flags, pure),
        );
        dst
    }
}

/// Viewing `a` as a vector of 8 `u32`s, copy the odd elements into the even elements below them,
/// then merge with `src` according to the mask provided. In other words, for all `0 <= i < 4`, set
/// the even elements according to `res[2 * i] := if k[2 * i] { a[2 * i + 1] } else { src[2 * i] }`,
/// and the odd elements according to
/// `res[2 * i + 1] := if k[2 * i + 1] { a[2 * i + 1] } else { src[2 * i + 1] }`.
#[inline]
#[must_use]
fn mask_movehdup_epi32_256(src: __m256i, k: __mmask8, a: __m256i) -> __m256i {
    // The instruction is only available in the floating-point flavor; this distinction is only for
    // historical reasons and no longer matters.

    // While we can write this using intrinsics, when inlined, the intrinsic often compiles
    // to a vpermt2ps which has worse latency, see https://godbolt.org/z/489aaPhz3.
    // Hence we use inline assembly to force the compiler to do the right thing.
    unsafe {
        let dst: __m256i;
        asm!(
            "vmovshdup {src_dst}{{{k}}}, {a}",
            src_dst = inlateout(ymm_reg) src => dst,
            k = in(kreg) k,
            a = in(ymm_reg) a,
            options(nomem, nostack, preserves_flags, pure),
        );
        dst
    }
}

/// Multiply a vector of unsigned field elements return a vector of unsigned field elements lying in [0, P).
///
/// Note that the input does not need to be in canonical form but must satisfy
/// the bound `lhs * rhs < 2^32 * P`. If this bound is not satisfied, the result
/// is undefined.
#[inline]
#[must_use]
fn mul<MPAVX512: MontyParametersAVX512>(lhs: __m512i, rhs: __m512i) -> __m512i {
    // We want this to compile to:
    //      vmovshdup  lhs_odd, lhs
    //      vmovshdup  rhs_odd, rhs
    //      vpmuludq   prod_evn, lhs, rhs
    //      vpmuludq   prod_hi, lhs_odd, rhs_odd
    //      vpmuludq   q_evn, prod_evn, MU
    //      vpmuludq   q_odd, prod_hi, MU
    //      vmovshdup  prod_hi{EVENS}, prod_evn
    //      vpmuludq   q_p_evn, q_evn, P
    //      vpmuludq   q_p_hi, q_odd, P
    //      vmovshdup  q_p_hi{EVENS}, q_p_evn
    //      vpcmpltud  underflow, prod_hi, q_p_hi
    //      vpsubd     res, prod_hi, q_p_hi
    //      vpaddd     res{underflow}, res, P
    // throughput: 6.5 cyc/vec (2.46 els/cyc)
    // latency: 21 cyc
    unsafe {
        // `vpmuludq` only reads the even doublewords, so when we pass `lhs` and `rhs` directly we
        // get the eight products at even positions.
        let lhs_evn = lhs;
        let rhs_evn = rhs;

        // Copy the odd doublewords into even positions to compute the eight products at odd
        // positions.
        // NB: The odd doublewords are ignored by `vpmuludq`, so we have a lot of choices for how to
        // do this; `vmovshdup` is nice because it runs on a memory port if the operand is in
        // memory, thus improving our throughput.
        let lhs_odd = movehdup_epi32(lhs);
        let rhs_odd = movehdup_epi32(rhs);

        let prod_evn = x86_64::_mm512_mul_epu32(lhs_evn, rhs_evn);
        let prod_odd = x86_64::_mm512_mul_epu32(lhs_odd, rhs_odd);

        // We throw a confuse compiler here to prevent the compiler from
        // using vpmullq instead of vpmuludq in the computations for q_p.
        // vpmullq has both higher latency and lower throughput.
        let q_evn = confuse_compiler(x86_64::_mm512_mul_epu32(prod_evn, MPAVX512::PACKED_MU));
        let q_odd = confuse_compiler(x86_64::_mm512_mul_epu32(prod_odd, MPAVX512::PACKED_MU));

        // Get all the high halves as one vector: this is `(lhs * rhs) >> 32`.
        // NB: `vpermt2d` may feel like a more intuitive choice here, but it has much higher
        // latency.
        let prod_hi = mask_movehdup_epi32(prod_odd, EVENS, prod_evn);

        // Normally we'd want to mask to perform % 2**32, but the instruction below only reads the
        // low 32 bits anyway.
        let q_p_evn = x86_64::_mm512_mul_epu32(q_evn, MPAVX512::PACKED_P);
        let q_p_odd = x86_64::_mm512_mul_epu32(q_odd, MPAVX512::PACKED_P);

        // We can ignore all the low halves of `q_p` as they cancel out. Get all the high halves as
        // one vector.
        let q_p_hi = mask_movehdup_epi32(q_p_odd, EVENS, q_p_evn);

        // Subtraction `prod_hi - q_p_hi` modulo `P`.
        // NB: Normally we'd `vpaddd P` and take the `vpminud`, but `vpminud` runs on port 0, which
        // is already under a lot of pressure performing multiplications. To relieve this pressure,
        // we check for underflow to generate a mask, and then conditionally add `P`. The underflow
        // check runs on port 5, increasing our throughput, although it does cost us an additional
        // cycle of latency.
        let underflow = x86_64::_mm512_cmplt_epu32_mask(prod_hi, q_p_hi);
        let t = x86_64::_mm512_sub_epi32(prod_hi, q_p_hi);
        x86_64::_mm512_mask_add_epi32(t, underflow, t, MPAVX512::PACKED_P)
    }
}

/// Multiply a vector of unsigned field elements by a single field element.
///
/// Return a vector of unsigned field elements lying in [0, P).
///
/// Note that the input does not need to be in canonical form but must satisfy
/// the bound `lhs * rhs < 2^32 * P`. If this bound is not satisfied, the result
/// is undefined.
#[inline]
#[must_use]
fn mul_256<MPAVX512: MontyParametersAVX512>(lhs: __m256i, rhs: i32) -> __m256i {
    // We want this to compile to:
    //      vmovshdup  lhs_odd, lhs
    //      vpbroadcastd  rhs, rhs
    //      vpmuludq   prod_evn, lhs, rhs
    //      vpmuludq   prod_hi, lhs_odd, rhs_odd
    //      vpmuludq   q_evn, prod_evn, MU
    //      vpmuludq   q_odd, prod_hi, MU
    //      vmovshdup  prod_hi{EVENS}, prod_evn
    //      vpmuludq   q_p_evn, q_evn, P
    //      vpmuludq   q_p_hi, q_odd, P
    //      vmovshdup  q_p_hi{EVENS}, q_p_evn
    //      vpcmpltud  underflow, prod_hi, q_p_hi
    //      vpsubd     res, prod_hi, q_p_hi
    //      vpaddd     res{underflow}, res, P
    // throughput: 6.5 cyc/vec (2.46 els/cyc)
    // latency: 21 cyc
    unsafe {
        // `vpmuludq` only reads the even doublewords, so when we pass `lhs` directly we
        // get the four products at even positions.
        let lhs_evn = lhs;
        let rhs = x86_64::_mm256_set1_epi32(rhs);

        // Copy the odd doublewords into even positions to compute the four products at odd
        // positions.
        // NB: The odd doublewords are ignored by `vpmuludq`, so we have a lot of choices for how to
        // do this; `vmovshdup` is nice because it runs on a memory port if the operand is in
        // memory, thus improving our throughput.
        let lhs_odd = movehdup_epi32_256(lhs);

        let prod_evn = x86_64::_mm256_mul_epu32(lhs_evn, rhs);
        let prod_odd = x86_64::_mm256_mul_epu32(lhs_odd, rhs);

        let mu_256 = x86_64::_mm512_castsi512_si256(MPAVX512::PACKED_MU);
        let q_evn = confuse_compiler_256(x86_64::_mm256_mul_epu32(prod_evn, mu_256));
        let q_odd = confuse_compiler_256(x86_64::_mm256_mul_epu32(prod_odd, mu_256));

        // Get all the high halves as one vector: this is `(lhs * rhs) >> 32`.
        // NB: `vpermt2d` may feel like a more intuitive choice here, but it has much higher
        // latency.
        let prod_hi = mask_movehdup_epi32_256(prod_odd, EVENS_8, prod_evn);

        // Normally we'd want to mask to perform % 2**32, but the instruction below only reads the
        // low 32 bits anyway.
        let p_256 = x86_64::_mm512_castsi512_si256(MPAVX512::PACKED_P);
        let q_p_evn = x86_64::_mm256_mul_epu32(q_evn, p_256);
        let q_p_odd = x86_64::_mm256_mul_epu32(q_odd, p_256);

        // We can ignore all the low halves of `q_p` as they cancel out. Get all the high halves as
        // one vector.
        let q_p_hi = mask_movehdup_epi32_256(q_p_odd, EVENS_8, q_p_evn);

        // Subtraction `prod_hi - q_p_hi` modulo `P`.
        // NB: Normally we'd `vpaddd P` and take the `vpminud`, but `vpminud` runs on port 0, which
        // is already under a lot of pressure performing multiplications. To relieve this pressure,
        // we check for underflow to generate a mask, and then conditionally add `P`. The underflow
        // check runs on port 5, increasing our throughput, although it does cost us an additional
        // cycle of latency.
        let underflow = x86_64::_mm256_cmplt_epu32_mask(prod_hi, q_p_hi);
        let t = x86_64::_mm256_sub_epi32(prod_hi, q_p_hi);
        x86_64::_mm256_mask_add_epi32(t, underflow, t, p_256)
    }
}

/// Compute the elementary arithmetic generalization of `xor`, namely `xor(l, r) = l + r - 2lr` of
/// Compute the elementary arithmetic generalization of `andnot`, namely `andn(l, r) = (1 - l)r` of
/// vectors in canonical form.
///
/// Inputs are assumed to be in canonical form, if the inputs are not in canonical form, the result is undefined.
#[inline]
#[must_use]
fn andn<MPAVX512: MontyParametersAVX512>(lhs: __m512i, rhs: __m512i) -> __m512i {
    // As we are working with MONTY_CONSTANT = 2^32, the internal representation
    // of 1 is 2^32 mod P = 2^32 - P mod P. Hence we compute (2^32 - P - l)r.
    // This product is less than 2^32P so we can apply our monty reduction to this.
    //
    // We want this to compile to:
    //      vpsubd     neg_lhs, 2^32 - P, lhs
    //      vmovshdup  lhs_odd, neg_lhs
    //      vmovshdup  rhs_odd, rhs
    //      vpmuludq   prod_evn, neg_lhs, rhs
    //      vpmuludq   prod_hi, lhs_odd, rhs_odd
    //      vpmuludq   q_evn, prod_evn, MU
    //      vpmuludq   q_odd, prod_hi, MU
    //      vmovshdup  prod_hi{EVENS}, prod_evn
    //      vpmuludq   q_p_evn, q_evn, P
    //      vpmuludq   q_p_hi, q_odd, P
    //      vmovshdup  q_p_hi{EVENS}, q_p_evn
    //      vpcmpltud  underflow, prod_hi, q_p_hi
    //      vpsubd     res, prod_hi, q_p_hi
    //      vpaddd     res{underflow}, res, P
    // throughput: 7 cyc/vec (2.3 els/cyc)
    // latency: 22 cyc
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
        // Use `mm512_mod_sub` to do the subtraction correctly mod P for any
        // `P < 2^32`.
        let one_monty = x86_64::_mm512_sub_epi32(x86_64::_mm512_setzero_epi32(), MPAVX512::PACKED_P);
        let neg_lhs = mm512_mod_sub(one_monty, lhs, MPAVX512::PACKED_P);

        // `neg_lhs` is canonical in [0, P), so `neg_lhs * rhs < 2^32 * P`.
        mul::<MPAVX512>(neg_lhs, rhs)
    }
}

/// Negate a vector of MontyField31 elements in canonical form.
/// If the inputs are not in canonical form, the result is undefined.
#[inline]
#[must_use]
fn neg<MPAVX512: MontyParametersAVX512>(val: __m512i) -> __m512i {
    // We want this to compile to:
    //      vptestmd  nonzero, val, val
    //      vpsubd    res{nonzero}{z}, P, val
    // throughput: 1 cyc/vec (16 els/cyc)
    // latency: 4 cyc

    // NB: This routine prioritizes throughput over latency. An alternative method would be to do
    // sub(0, val), which would result in shorter latency, but also lower throughput.

    //   If val is nonzero, then val is in {1, ..., P - 1} and P - val is in the same range. If val
    // is zero, then the result is zeroed by masking.
    unsafe {
        // Safety: If this code got compiled then AVX-512F intrinsics are available.
        let nonzero = x86_64::_mm512_test_epi32_mask(val, val);
        x86_64::_mm512_maskz_sub_epi32(nonzero, MPAVX512::PACKED_P, val)
    }
}

/// Lets us combine some code for MontyField31<FP> and PackedMontyField31AVX2<FP> elements.
///
/// Provides methods to convert an element into a __m512i element and then shift this __m512i
/// element so that the odd elements now lie in the even positions. Depending on the type of input,
/// the shift might be a no-op.
trait IntoM512<PMP: PackedMontyParameters>: Copy + Into<PackedMontyField31AVX512<PMP>> {
    /// Convert the input into a __m512i element.
    fn as_m512i(&self) -> __m512i;

    /// Convert the input to a __m512i element and shift so that all elements in odd positions
    /// now lie in even positions.
    ///
    /// The values lying in the even positions are undefined.
    #[inline(always)]
    fn as_shifted_m512i(&self) -> __m512i {
        let vec = self.as_m512i();
        movehdup_epi32(vec)
    }
}

impl<PMP: PackedMontyParameters> IntoM512<PMP> for PackedMontyField31AVX512<PMP> {
    #[inline(always)]
    fn as_m512i(&self) -> __m512i {
        self.to_vector()
    }
}

impl<PMP: PackedMontyParameters> IntoM512<PMP> for MontyField31<PMP> {
    #[inline(always)]
    fn as_m512i(&self) -> __m512i {
        unsafe { x86_64::_mm512_set1_epi32(self.value as i32) }
    }

    #[inline(always)]
    fn as_shifted_m512i(&self) -> __m512i {
        unsafe { x86_64::_mm512_set1_epi32(self.value as i32) }
    }
}

/// Compute the elementary function `l0*r0 + l1*r1` given four inputs
/// in canonical form.
///
/// If the inputs are not in canonical form, the result is undefined.
#[inline]
#[must_use]
#[allow(private_bounds)]
pub fn dot_product_2<PMP: PackedMontyParameters, LHS: IntoM512<PMP>, RHS: IntoM512<PMP>>(
    lhs: [LHS; 2],
    rhs: [RHS; 2],
) -> __m512i {
    // The following analysis treats all input arrays as being arrays of PackedMontyField31AVX512<FP>.
    // If one of the arrays contains MontyField31<FP>, we get to avoid the initial vmovshdup.
    //
    // We improve the throughput by combining the monty reductions together. As all inputs are
    // `< P < 2^{31}`, `l0*r0 + l1*r1 < 2P^2 < 2^{32}P` so the montgomery reduction
    // algorithm can be applied to the sum of the products instead of to each product individually.
    //
    // We want this to compile to:
    //      vmovshdup  lhs_odd0, lhs0
    //      vmovshdup  rhs_odd0, rhs0
    //      vmovshdup  lhs_odd1, lhs1
    //      vmovshdup  rhs_odd1, rhs1
    //      vpmuludq   prod_evn0, lhs0, rhs0
    //      vpmuludq   prod_odd0, lhs_odd0, rhs_odd0
    //      vpmuludq   prod_evn1, lhs1, rhs1
    //      vpmuludq   prod_odd1, lhs_odd1, rhs_odd1
    //      vpaddq     dot_evn, prod_evn0, prod_evn1
    //      vpaddq     dot, prod_odd0, prod_odd1
    //      vpmuludq   q_evn, prod_evn, MU
    //      vpmuludq   q_odd, dot, MU
    //      vpmuludq   q_P_evn, q_evn, P
    //      vpmuludq   q_P, q_odd, P
    //      vmovshdup  dot{EVENS} dot_evn
    //      vmovshdup  q_P{EVENS} q_P_evn
    //      vpcmpltud  underflow, dot, q_P
    //      vpsubd     res, dot, q_P
    //      vpaddd     res{underflow}, res, P
    // throughput: 9.5 cyc/vec (1.68 els/cyc)
    // latency: 22 cyc
    unsafe {
        let lhs_evn0 = lhs[0].as_m512i();
        let lhs_odd0 = lhs[0].as_shifted_m512i();
        let lhs_evn1 = lhs[1].as_m512i();
        let lhs_odd1 = lhs[1].as_shifted_m512i();

        let rhs_evn0 = rhs[0].as_m512i();
        let rhs_odd0 = rhs[0].as_shifted_m512i();
        let rhs_evn1 = rhs[1].as_m512i();
        let rhs_odd1 = rhs[1].as_shifted_m512i();

        let mul_evn0 = x86_64::_mm512_mul_epu32(lhs_evn0, rhs_evn0);
        let mul_evn1 = x86_64::_mm512_mul_epu32(lhs_evn1, rhs_evn1);
        let mul_odd0 = x86_64::_mm512_mul_epu32(lhs_odd0, rhs_odd0);
        let mul_odd1 = x86_64::_mm512_mul_epu32(lhs_odd1, rhs_odd1);

        let dot_evn = x86_64::_mm512_add_epi64(mul_evn0, mul_evn1);
        let dot_odd = x86_64::_mm512_add_epi64(mul_odd0, mul_odd1);

        // We throw a confuse compiler here to prevent the compiler from
        // using vpmullq instead of vpmuludq in the computations for q_p.
        // vpmullq has both higher latency and lower throughput.
        let q_evn = confuse_compiler(x86_64::_mm512_mul_epu32(dot_evn, PMP::PACKED_MU));
        let q_odd = confuse_compiler(x86_64::_mm512_mul_epu32(dot_odd, PMP::PACKED_MU));

        // Get all the high halves as one vector: this is `dot(lhs, rhs) >> 32`.
        // NB: `vpermt2d` may feel like a more intuitive choice here, but it has much higher
        // latency.
        let dot = mask_movehdup_epi32(dot_odd, EVENS, dot_evn);

        // Normally we'd want to mask to perform % 2**32, but the instruction below only reads the
        // low 32 bits anyway.
        let q_p_evn = x86_64::_mm512_mul_epu32(q_evn, PMP::PACKED_P);
        let q_p_odd = x86_64::_mm512_mul_epu32(q_odd, PMP::PACKED_P);

        // We can ignore all the low halves of `q_p` as they cancel out. Get all the high halves as
        // one vector.
        let q_p = mask_movehdup_epi32(q_p_odd, EVENS, q_p_evn);

        // Subtraction `prod_hi - q_p_hi` modulo `P`.
        // NB: Normally we'd `vpaddd P` and take the `vpminud`, but `vpminud` runs on port 0, which
        // is already under a lot of pressure performing multiplications. To relieve this pressure,
        // we check for underflow to generate a mask, and then conditionally add `P`. The underflow
        // check runs on port 5, increasing our throughput, although it does cost us an additional
        // cycle of latency.
        let underflow = x86_64::_mm512_cmplt_epu32_mask(dot, q_p);
        let t = x86_64::_mm512_sub_epi32(dot, q_p);
        x86_64::_mm512_mask_add_epi32(t, underflow, t, PMP::PACKED_P)
    }
}

// `dot_product_4` was a specialised batched-Montgomery dot product that
// accumulated four 64-bit products into a single u64 before reduction. That
// bound only holds for `P < 2^31`; for the current 32-bit prime even two
// products overflow u64. `general_dot_product` falls through to scalar
// accumulation via the canonical Mul instead.

/// A general fast dot product implementation.
///
/// `dot_product_2` / `dot_product_4` would normally amortise one Montgomery
/// reduction over multiple products, but they accumulate two/four 64-bit
/// products into a single u64 — sound only for `P < 2^31`. For the current
/// 32-bit prime (`0xfa000001`) even two products can overflow u64, so we
/// reduce each product individually and accumulate the canonical results.
#[inline(always)]
fn general_dot_product<FP: FieldParameters, LHS: IntoM512<FP>, RHS: IntoM512<FP>, const N: usize>(
    lhs: &[LHS],
    rhs: &[RHS],
) -> PackedMontyField31AVX512<FP> {
    assert_eq!(lhs.len(), N);
    assert_eq!(rhs.len(), N);
    if N == 0 {
        return PackedMontyField31AVX512::<FP>::ZERO;
    }
    let mut acc: PackedMontyField31AVX512<FP> = lhs[0].into() * rhs[0].into();
    for i in 1..N {
        acc += lhs[i].into() * rhs[i].into();
    }
    acc
}

impl_packed_value!(
    PackedMontyField31AVX512,
    MontyField31,
    WIDTH,
    (PackedMontyParameters, PMP)
);

unsafe impl<FP: FieldParameters> PackedField for PackedMontyField31AVX512<FP> {
    type Scalar = MontyField31<FP>;

    #[inline]
    fn packed_linear_combination<const N: usize>(coeffs: &[Self::Scalar], vecs: &[Self]) -> Self {
        general_dot_product::<_, _, _, N>(coeffs, vecs)
    }
}

impl_packed_field_pow_2!(
    PackedMontyField31AVX512, (FieldParameters, FP);
    [
        (1, interleave_u32),
        (2, interleave_u64),
        (4, interleave_u128),
        (8, interleave_u256)
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
            // This could likely be sped up by a completely custom implementation of mul.
            // Surprisingly, the current version is only slightly faster than:
            // res.iter_mut().zip(a.iter()).for_each(|(r, a)| *r = *a * b);
            let out: [MontyField31<FP>; 8] = unsafe {
                let lhs: __m256i = transmute([a[0].value, a[1].value, a[2].value, a[3].value, 0, 0, 0, 0]);
                let prod = mul_256::<FP>(lhs, b.value as i32);
                transmute(prod)
            };

            res.copy_from_slice(&out[..4]);
        }
        5 => {
            // This could likely be sped up by a completely custom implementation of mul.
            let out: [MontyField31<FP>; 8] = unsafe {
                let lhs: __m256i = transmute([a[0].value, a[1].value, a[2].value, a[3].value, a[4].value, 0, 0, 0]);
                let prod = mul_256::<FP>(lhs, b.value as i32);
                transmute(prod)
            };

            res.copy_from_slice(&out[..5]);
        }
        8 => {
            // This could likely be sped up by a completely custom implementation of mul.
            let out: [MontyField31<FP>; 8] = unsafe {
                let lhs: __m256i = transmute([
                    a[0].value, a[1].value, a[2].value, a[3].value, a[4].value, a[5].value, a[6].value, a[7].value,
                ]);
                let prod = mul_256::<FP>(lhs, b.value as i32);
                transmute(prod)
            };

            res.copy_from_slice(&out);
        }
        _ => panic!("Unsupported binomial extension degree: {}", WIDTH),
    }
}
