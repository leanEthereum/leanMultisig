// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use alloc::vec::Vec;
use core::arch::aarch64::{self, int32x4_t, uint32x4_t, uint64x2_t};
use core::arch::asm;
use core::hint::unreachable_unchecked;
use core::iter::{Product, Sum};
use core::mem::transmute;
use core::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use field::interleave::{interleave_u32, interleave_u64};
use field::op_assign_macros::{
    impl_add_assign, impl_add_base_field, impl_div_methods, impl_mul_base_field, impl_mul_methods, impl_packed_value,
    impl_rng, impl_sub_assign, impl_sub_base_field, impl_sum_prod_base_field, ring_sum,
};
use field::{
    Algebra, Field, InjectiveMonomial, PackedField, PackedFieldPow2, PackedValue, PermutationMonomial,
    PrimeCharacteristicRing, impl_packed_field_pow_2, uint32x4_mod_add, uint32x4_mod_sub,
};
use rand::Rng;
use rand::distr::{Distribution, StandardUniform};
use utils::reconstitute_from_base;

use super::utils::halve_neon;
use crate::{FieldParameters, MontyField31, PackedMontyParameters, RelativelyPrimePower};

const WIDTH: usize = 4;

pub trait MontyParametersNeon {
    const PACKED_P: uint32x4_t;
    const PACKED_MU: int32x4_t;
}

/// A trait to allow functions to be generic over scalar `MontyField31` and packed `PackedMontyField31Neon`.
trait IntoVec<P: PackedMontyParameters>: Copy {
    /// Convert the value to a NEON vector, broadcasting if it's a scalar.
    fn into_vec(self) -> uint32x4_t;
}

impl<P: PackedMontyParameters> IntoVec<P> for PackedMontyField31Neon<P> {
    #[inline(always)]
    fn into_vec(self) -> uint32x4_t {
        self.to_vector()
    }
}

impl<P: PackedMontyParameters> IntoVec<P> for MontyField31<P> {
    #[inline(always)]
    fn into_vec(self) -> uint32x4_t {
        // Broadcast the scalar value to all lanes of the vector.
        unsafe { aarch64::vdupq_n_u32(self.value) }
    }
}

/// Vectorized NEON implementation of `MontyField31` arithmetic.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
#[repr(transparent)] // Needed to make `transmute`s safe.
#[must_use]
pub struct PackedMontyField31Neon<PMP: PackedMontyParameters>(pub [MontyField31<PMP>; WIDTH]);

impl<PMP: PackedMontyParameters> PackedMontyField31Neon<PMP> {
    /// Get an arch-specific vector representing the packed values.
    #[inline]
    #[must_use]
    pub(crate) fn to_vector(self) -> uint32x4_t {
        unsafe {
            // Safety: `MontyField31` is `repr(transparent)` so it can be transmuted to `u32`. It
            // follows that `[MontyField31; WIDTH]` can be transmuted to `[u32; WIDTH]`, which can be
            // transmuted to `uint32x4_t`, since arrays are guaranteed to be contiguous in memory.
            // Finally `PackedMontyField31Neon` is `repr(transparent)` so it can be transmuted to
            // `[MontyField31; WIDTH]`.
            transmute(self)
        }
    }

    /// Get an arch-specific vector representing the packed values.
    #[inline]
    #[must_use]
    pub(crate) fn to_signed_vector(self) -> int32x4_t {
        unsafe {
            // Safety: `MontyField31` is `repr(transparent)` so it can be transmuted to `u32` furthermore
            // the u32 is guaranteed to be less than `2^31` so it can be safely reinterpreted as an `i32`. It
            // follows that `[MontyField31; WIDTH]` can be transmuted to `[i32; WIDTH]`, which can be
            // transmuted to `int32x4_t`, since arrays are guaranteed to be contiguous in memory.
            // Finally `PackedMontyField31Neon` is `repr(transparent)` so it can be transmuted to
            // `[MontyField31; WIDTH]`.
            transmute(self)
        }
    }

    /// Make a packed field vector from an arch-specific vector.
    ///
    /// SAFETY: The caller must ensure that each element of `vector` represents a valid `MontyField31`.
    /// In particular, each element of vector must be in `0..P` (canonical form).
    #[inline]
    pub(crate) unsafe fn from_vector(vector: uint32x4_t) -> Self {
        unsafe {
            // Safety: It is up to the user to ensure that elements of `vector` represent valid
            // `MontyField31` values. We must only reason about memory representations. `uint32x4_t` can be
            // transmuted to `[u32; WIDTH]` (since arrays elements are contiguous in memory), which can
            // be transmuted to `[MontyField31; WIDTH]` (since `MontyField31` is `repr(transparent)`), which in
            // turn can be transmuted to `PackedMontyField31Neon` (since `PackedMontyField31Neon` is also
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
}

impl<PMP: PackedMontyParameters> From<MontyField31<PMP>> for PackedMontyField31Neon<PMP> {
    #[inline]
    fn from(value: MontyField31<PMP>) -> Self {
        Self::broadcast(value)
    }
}

impl<PMP: PackedMontyParameters> Add for PackedMontyField31Neon<PMP> {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        let lhs = self.to_vector();
        let rhs = rhs.to_vector();
        let res = uint32x4_mod_add(lhs, rhs, PMP::PACKED_P);
        unsafe {
            // Safety: `uint32x4_mod_add` returns values in canonical form when given values in canonical form.
            Self::from_vector(res)
        }
    }
}

impl<PMP: PackedMontyParameters> Sub for PackedMontyField31Neon<PMP> {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Self) -> Self {
        let lhs = self.to_vector();
        let rhs = rhs.to_vector();
        let res = uint32x4_mod_sub(lhs, rhs, PMP::PACKED_P);
        unsafe {
            // Safety: `uint32x4_mod_sub` returns values in canonical form when given values in canonical form.
            Self::from_vector(res)
        }
    }
}

impl<PMP: PackedMontyParameters> Neg for PackedMontyField31Neon<PMP> {
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

impl<PMP: PackedMontyParameters> Mul for PackedMontyField31Neon<PMP> {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        let lhs = self.to_vector();
        let rhs = rhs.to_vector();
        let res = mul_unsigned::<PMP>(lhs, rhs);
        unsafe {
            // Safety: `mul_unsigned` returns values in canonical form when given values in canonical form.
            Self::from_vector(res)
        }
    }
}

impl_add_assign!(PackedMontyField31Neon, (PackedMontyParameters, PMP));
impl_sub_assign!(PackedMontyField31Neon, (PackedMontyParameters, PMP));
impl_mul_methods!(PackedMontyField31Neon, (FieldParameters, FP));
ring_sum!(PackedMontyField31Neon, (FieldParameters, FP));
impl_rng!(PackedMontyField31Neon, (PackedMontyParameters, PMP));

impl<FP: FieldParameters> PrimeCharacteristicRing for PackedMontyField31Neon<FP> {
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
        let halved = halve_neon::<FP>(val);
        unsafe {
            // Safety: `halve_neon` returns values in canonical form when given values in canonical form.
            Self::from_vector(halved)
        }
    }

    #[inline]
    fn cube(&self) -> Self {
        let val = self.to_vector();
        let res = cube_unsigned::<FP>(val);
        unsafe {
            // Safety: `cube_unsigned` returns values in canonical form when given values in canonical form.
            Self::from_vector(res)
        }
    }

    #[inline(always)]
    fn dot_product<const N: usize>(u: &[Self; N], v: &[Self; N]) -> Self {
        general_dot_product::<_, _, _, N>(u, v)
    }

    #[inline(always)]
    fn zero_vec(len: usize) -> Vec<Self> {
        // SAFETY: this is a repr(transparent) wrapper around an array.
        unsafe { reconstitute_from_base(MontyField31::<FP>::zero_vec(len * WIDTH)) }
    }

    #[inline(always)]
    fn exp_const_u64<const POWER: u64>(&self) -> Self {
        // We provide specialised code for the powers 3, 5, 7 as these turn up regularly.
        // The other powers could be specialised similarly but we ignore this for now.
        match POWER {
            0 => Self::ONE,
            1 => *self,
            2 => self.square(),
            3 => self.cube(),
            4 => self.square().square(),
            5 => {
                let val = self.to_vector();
                unsafe {
                    let res = exp_5_unsigned::<FP>(val);
                    Self::from_vector(res)
                }
            }
            6 => self.square().cube(),
            7 => {
                let val = self.to_vector();
                unsafe {
                    let res = exp_7_unsigned::<FP>(val);
                    Self::from_vector(res)
                }
            }
            _ => self.exp_u64(POWER),
        }
    }
}

impl_add_base_field!(PackedMontyField31Neon, MontyField31, (PackedMontyParameters, PMP));
impl_sub_base_field!(PackedMontyField31Neon, MontyField31, (PackedMontyParameters, PMP));
impl_mul_base_field!(PackedMontyField31Neon, MontyField31, (PackedMontyParameters, PMP));
impl_div_methods!(PackedMontyField31Neon, MontyField31, (FieldParameters, FP));
impl_sum_prod_base_field!(PackedMontyField31Neon, MontyField31, (FieldParameters, FP));

impl<FP: FieldParameters> Algebra<MontyField31<FP>> for PackedMontyField31Neon<FP> {}

impl<FP: FieldParameters> PackedMontyField31Neon<FP> {
    /// Compute the dot product of a packed vector with a scalar vector.
    ///
    /// This is more efficient than broadcasting the scalars first, because the
    /// Karatsuba recursion can keep the constant (rhs) side as cheap scalar
    /// operations while only the lhs/output side uses SIMD.
    #[inline(always)]
    pub fn mixed_dot_product<const N: usize>(lhs: &[Self; N], rhs: &[MontyField31<FP>; N]) -> Self {
        general_dot_product::<_, _, _, N>(lhs, rhs)
    }
}

impl<FP: FieldParameters + RelativelyPrimePower<D>, const D: u64> InjectiveMonomial<D> for PackedMontyField31Neon<FP> {}

impl<FP: FieldParameters + RelativelyPrimePower<D>, const D: u64> PermutationMonomial<D>
    for PackedMontyField31Neon<FP>
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
fn confuse_compiler(x: uint32x4_t) -> uint32x4_t {
    let y;
    unsafe {
        asm!(
            "/*{0:v}*/",
            inlateout(vreg) x => y,
            options(nomem, nostack, preserves_flags, pure),
        );
        // Below tells the compiler the semantics of this so it can still do constant folding, etc.
        // You may ask, doesn't it defeat the point of the inline asm block to tell the compiler
        // what it does? The answer is that we still inhibit the transform we want to avoid, so
        // apparently not. Idk, LLVM works in mysterious ways.
        if transmute::<uint32x4_t, [u32; 4]>(x) != transmute::<uint32x4_t, [u32; 4]>(y) {
            unreachable_unchecked();
        }
    }
    y
}

// MONTGOMERY MULTIPLICATION
//   This implementation is based on [1] but with changes. The reduction is as follows:
//
// Constants: P < 2^31
//            B = 2^32
//            μ = P^-1 mod B
// Input: -P^2 <= C <= P^2
// Output: -P < D < P such that D = C B^-1 (mod P)
// Define:
//   smod_B(a) = r, where -B/2 <= r <= B/2 - 1 and r = a (mod B).
// Algorithm:
//   1. Q := smod_B(μ C)
//   2. D := (C - Q P) / B
//
// We first show that the division in step 2. is exact. It suffices to show that C = Q P (mod B). By
// definition of Q, smod_B, and μ, we have Q P = smod_B(μ C) P = μ C P = P^-1 C P = C (mod B).
//
// We also have C - Q P = C (mod P), so thus D = C B^-1 (mod P).
//
// It remains to show that D is in the correct range. It suffices to show that -P B < C - Q P < P B.
// We know that -P^2 <= C <= P^2 and (-B / 2) P <= Q P <= (B/2 - 1) P. Then
// (1 - B/2) P - P^2 <= C - Q P <= (B/2) P + P^2. Now, P < B/2, so B/2 + P < B and
// (B/2) P + P^2 < P B; also B/2 - 1 + P < B, so -P B < (1 - B/2) P - P^2.
// Hence, -P B < C - Q P < P B as desired.
//
// [1] Modern Computer Arithmetic, Richard Brent and Paul Zimmermann, Cambridge University Press,
//     2010, algorithm 2.7.

#[inline]
#[must_use]
fn mulby_mu<MPNeon: MontyParametersNeon>(val: int32x4_t) -> int32x4_t {
    // We want this to compile to:
    //      mul      res.4s, val.4s, MU.4s
    // throughput: .25 cyc/vec (16 els/cyc)
    // latency: 3 cyc

    unsafe { aarch64::vmulq_s32(val, MPNeon::PACKED_MU) }
}

#[inline]
#[must_use]
fn get_c_hi(lhs: int32x4_t, rhs: int32x4_t) -> int32x4_t {
    // We want this to compile to:
    //      sqdmulh  c_hi.4s, lhs.4s, rhs.4s
    // throughput: .25 cyc/vec (16 els/cyc)
    // latency: 3 cyc

    unsafe {
        // Get bits 31, ..., 62 of C. Note that `sqdmulh` saturates when the product doesn't fit in
        // an `i63`, but this cannot happen here due to our bounds on `lhs` and `rhs`.
        aarch64::vqdmulhq_s32(lhs, rhs)
    }
}

#[inline]
#[must_use]
fn get_qp_hi<MPNeon: MontyParametersNeon>(lhs: int32x4_t, mu_rhs: int32x4_t) -> int32x4_t {
    // We want this to compile to:
    //      mul      q.4s, lhs.4s, mu_rhs.4s
    //      sqdmulh  qp_hi.4s, q.4s, P.4s
    // throughput: .5 cyc/vec (8 els/cyc)
    // latency: 6 cyc

    unsafe {
        // Form `Q`.
        let q = aarch64::vmulq_s32(lhs, mu_rhs);

        // Gets bits 31, ..., 62 of Q P. Again, saturation is not an issue because `P` is not
        // -2**31.
        aarch64::vqdmulhq_s32(q, aarch64::vreinterpretq_s32_u32(MPNeon::PACKED_P))
    }
}

/// Montgomery reduction of a 64-bit product to canonical form [0, P).
///
/// Given C (64-bit unsigned per lane, split into low and high halves),
/// computes D = (C - Q*P) / 2^32 mod P where Q = C*MU mod 2^32.
///
/// # Safety
/// C must be < 2^32 * P per lane (guaranteed for a single product of values in [0, P)).
#[inline]
#[must_use]
unsafe fn monty_reduce_neon<MPNeon: MontyParametersNeon>(c_l: uint64x2_t, c_h: uint64x2_t) -> uint32x4_t {
    // Montgomery reduction: D = (C - Q*P) / 2^32, then canonicalize D ∈ (-P, P) → [0, P).
    //
    // Key trick: since C_lo ≡ (qP)_lo (mod 2^32) by construction, the 64-bit subtraction
    // d = C - qP has zero low 32 bits and the borrow propagation only affects the high word.
    // So: d_hi = c_hi - qp_hi (u32 wrapping), and borrow ↔ d_hi > c_hi (unsigned).
    //
    //      vuzp1     c_lo, c_l, c_h           // extract low 32 bits
    //      vuzp2     c_hi, c_l, c_h           // extract high 32 bits
    //      vmul      q, c_lo, MU              // q = c_lo * MU mod 2^32
    //      vmlsl     d_l, c_l, q_lo, P_lo     // d_l = c_l - q_lo*P_lo (64-bit)
    //      vmlsl2    d_h, c_h, q, P           // d_h = c_h - q_hi*P_hi (64-bit)
    //      vuzp2     d_hi, d_l, d_h           // extract D_u32
    //      cmhi      borrow, d_hi, c_hi       // borrow: d_hi > c_hi (unsigned 32-bit)
    //      and       corr, borrow, P
    //      add       result, d_hi, corr
    //
    // 9 instructions, throughput ~2.25 cyc/vec.
    unsafe {
        let c_lo = aarch64::vuzp1q_u32(aarch64::vreinterpretq_u32_u64(c_l), aarch64::vreinterpretq_u32_u64(c_h));
        let c_hi = aarch64::vuzp2q_u32(aarch64::vreinterpretq_u32_u64(c_l), aarch64::vreinterpretq_u32_u64(c_h));

        let mu = aarch64::vreinterpretq_u32_s32(MPNeon::PACKED_MU);
        let q = aarch64::vmulq_u32(c_lo, mu);

        let d_l = aarch64::vmlsl_u32(c_l, aarch64::vget_low_u32(q), aarch64::vget_low_u32(MPNeon::PACKED_P));
        let d_h = aarch64::vmlsl_high_u32(c_h, q, MPNeon::PACKED_P);

        let d_hi = aarch64::vuzp2q_u32(aarch64::vreinterpretq_u32_u64(d_l), aarch64::vreinterpretq_u32_u64(d_h));

        // Borrow ↔ d_hi > c_hi (unsigned 32-bit): the low 32 bits cancel in C - qP,
        // so the u64 borrow equals the u32 high-word borrow.
        let borrow = aarch64::vcgtq_u32(d_hi, c_hi);
        let corr = aarch64::vandq_u32(borrow, MPNeon::PACKED_P);
        aarch64::vaddq_u32(d_hi, corr)
    }
}

/// Multiply MontyField31 field elements (unsigned, works for P > 2^31).
///
/// Inputs must be unsigned 32-bit integers in [0, P).
/// Outputs will be unsigned 32-bit integers in canonical form [0, P).
#[inline]
#[must_use]
fn mul_unsigned<MPNeon: MontyParametersNeon>(lhs: uint32x4_t, rhs: uint32x4_t) -> uint32x4_t {
    unsafe {
        // Widening multiply: C = lhs * rhs (64-bit per lane)
        let c_l = aarch64::vmull_u32(aarch64::vget_low_u32(lhs), aarch64::vget_low_u32(rhs));
        let c_h = aarch64::vmull_high_u32(lhs, rhs);
        monty_reduce_neon::<MPNeon>(c_l, c_h)
    }
}

/// Take cube of MontyField31 field elements (unsigned path).
#[inline]
#[must_use]
fn cube_unsigned<MPNeon: MontyParametersNeon>(val: uint32x4_t) -> uint32x4_t {
    let val_2 = mul_unsigned::<MPNeon>(val, val);
    mul_unsigned::<MPNeon>(val_2, val)
}

/// Take the fifth power (unsigned path).
#[inline]
#[must_use]
fn exp_5_unsigned<MPNeon: MontyParametersNeon>(val: uint32x4_t) -> uint32x4_t {
    let val_2 = mul_unsigned::<MPNeon>(val, val);
    let val_3 = mul_unsigned::<MPNeon>(val_2, val);
    mul_unsigned::<MPNeon>(val_3, val_2)
}

/// Take the seventh power (unsigned path).
#[inline]
#[must_use]
fn exp_7_unsigned<MPNeon: MontyParametersNeon>(val: uint32x4_t) -> uint32x4_t {
    let val_2 = mul_unsigned::<MPNeon>(val, val);
    let val_3 = mul_unsigned::<MPNeon>(val_2, val);
    let val_4 = mul_unsigned::<MPNeon>(val_2, val_2);
    mul_unsigned::<MPNeon>(val_4, val_3)
}

/// Negate a vector of Monty31 field elements in canonical form.
/// If the inputs are not in canonical form, the result is undefined.
#[inline]
#[must_use]
fn neg<MPNeon: MontyParametersNeon>(val: uint32x4_t) -> uint32x4_t {
    // We want this to compile to:
    //      sub   t.4s, P.4s, val.4s
    //      cmeq  is_zero.4s, val.4s, #0
    //      bic   res.4s, t.4s, is_zero.4s
    // throughput: .75 cyc/vec (5.33 els/cyc)
    // latency: 4 cyc

    // This has the same throughput as `sub(0, val)` but slightly lower latency.

    //   We want to return (-val) mod P. This is equivalent to returning `0` if `val = 0` and
    // `P - val` otherwise, since `val` is in `0, ..., P - 1`.
    //   Let `t := P - val` and let `is_zero := (-1) mod 2^32` if `val = 0` and `0` otherwise.
    //   We return `r := t & ~is_zero`, which is `t` if `val > 0` and `0` otherwise, as desired.
    unsafe {
        // Safety: If this code got compiled then NEON intrinsics are available.
        let t = aarch64::vsubq_u32(MPNeon::PACKED_P, val);
        let is_zero = aarch64::vceqzq_u32(val);
        aarch64::vbicq_u32(t, is_zero)
    }
}

impl_packed_value!(
    PackedMontyField31Neon,
    MontyField31,
    WIDTH,
    (PackedMontyParameters, PMP)
);

unsafe impl<FP: FieldParameters> PackedField for PackedMontyField31Neon<FP> {
    type Scalar = MontyField31<FP>;

    #[inline]
    fn packed_linear_combination<const N: usize>(coeffs: &[Self::Scalar], vecs: &[Self]) -> Self {
        general_dot_product::<_, _, _, N>(coeffs, vecs)
    }

    /// Fused `(self - rhs) * scalar`.
    #[inline]
    fn fused_sub_mul(self, rhs: Self, scalar: Self::Scalar) -> Self {
        // With P > 2^31, we can't use the signed multiplication shortcut.
        // Fall back to sub + mul.
        let diff = self - rhs;
        let scalar_packed: Self = scalar.into();
        diff * scalar_packed
    }
}

impl_packed_field_pow_2!(
    PackedMontyField31Neon, (FieldParameters, FP);
    [
        (1, interleave_u32),
        (2, interleave_u64),
    ],
    WIDTH
);

/// Compute the elementary function `l0*r0 + l1*r1` given four inputs
/// in canonical form.
///
/// If the inputs are not in canonical form, the result is undefined.
#[inline]
unsafe fn dot_product_2<P, LHS, RHS>(lhs: &[LHS; 2], rhs: &[RHS; 2]) -> PackedMontyField31Neon<P>
where
    P: FieldParameters + MontyParametersNeon,
    LHS: IntoVec<P>,
    RHS: IntoVec<P>,
{
    unsafe {
        // Accumulate C = l0*r0 + l1*r1 in u64 (may overflow for P > 2^31).
        //
        // For P > 2^31: each product < P^2 ≈ 2^63.9, so 2 products can exceed 2^64.
        // We detect the u64 overflow and correct the Montgomery result afterwards.
        // Overflow correction: true_sum = u64_sum + 2^64, so D_true = D_naive + 2^32.
        // In the field: D_true ≡ D_naive + (2^32 mod P) = D_naive + (2^32 - P).
        // Since D_naive ∈ [0, P) and (2^32 - P) < P, the sum is in [0, 2P).
        // One conditional subtraction of P yields [0, P).

        // Low half: accumulate with overflow detection
        let prod0_l = aarch64::vmull_u32(
            aarch64::vget_low_u32(lhs[0].into_vec()),
            aarch64::vget_low_u32(rhs[0].into_vec()),
        );
        let sum_l = aarch64::vmlal_u32(
            prod0_l,
            aarch64::vget_low_u32(lhs[1].into_vec()),
            aarch64::vget_low_u32(rhs[1].into_vec()),
        );
        let over_l = aarch64::vcltq_u64(sum_l, prod0_l); // overflow: sum < prev

        // High half: same
        let prod0_h = aarch64::vmull_high_u32(lhs[0].into_vec(), rhs[0].into_vec());
        let sum_h = aarch64::vmlal_high_u32(prod0_h, lhs[1].into_vec(), rhs[1].into_vec());
        let over_h = aarch64::vcltq_u64(sum_h, prod0_h);

        // Montgomery reduction using 32-bit high-word borrow trick
        let c_lo = aarch64::vuzp1q_u32(
            aarch64::vreinterpretq_u32_u64(sum_l),
            aarch64::vreinterpretq_u32_u64(sum_h),
        );
        let c_hi = aarch64::vuzp2q_u32(
            aarch64::vreinterpretq_u32_u64(sum_l),
            aarch64::vreinterpretq_u32_u64(sum_h),
        );
        let q = aarch64::vmulq_u32(c_lo, aarch64::vreinterpretq_u32_s32(P::PACKED_MU));
        let d_l = aarch64::vmlsl_u32(sum_l, aarch64::vget_low_u32(q), aarch64::vget_low_u32(P::PACKED_P));
        let d_h = aarch64::vmlsl_high_u32(sum_h, q, P::PACKED_P);
        let d_hi = aarch64::vuzp2q_u32(aarch64::vreinterpretq_u32_u64(d_l), aarch64::vreinterpretq_u32_u64(d_h));
        let borrow = aarch64::vcgtq_u32(d_hi, c_hi);
        let mut d = aarch64::vaddq_u32(d_hi, aarch64::vandq_u32(borrow, P::PACKED_P));

        // Overflow correction: add (2^32 - P) where u64 overflow occurred
        let over = aarch64::vuzp2q_u32(
            aarch64::vreinterpretq_u32_u64(over_l),
            aarch64::vreinterpretq_u32_u64(over_h),
        );
        let neg_p = aarch64::vdupq_n_u32(0u32.wrapping_sub(P::PRIME)); // 2^32 - P
        d = aarch64::vaddq_u32(d, aarch64::vandq_u32(over, neg_p));

        // Final reduction from [0, 2P) → [0, P)
        let geq_p = aarch64::vcgeq_u32(d, P::PACKED_P);
        let canonical_res = aarch64::vsubq_u32(d, aarch64::vandq_u32(geq_p, P::PACKED_P));

        PackedMontyField31Neon::from_vector(canonical_res)
    }
}

/// A general fast dot product implementation using NEON.
#[inline(always)]
fn general_dot_product<P, LHS, RHS, const N: usize>(lhs: &[LHS], rhs: &[RHS]) -> PackedMontyField31Neon<P>
where
    P: FieldParameters + MontyParametersNeon,
    LHS: IntoVec<P> + Into<PackedMontyField31Neon<P>>,
    RHS: IntoVec<P> + Into<PackedMontyField31Neon<P>>,
{
    assert_eq!(lhs.len(), N);
    assert_eq!(rhs.len(), N);
    // For P > 2^31, we accumulate at most 2 products per Montgomery reduction (via dot_product_2
    // with u64 overflow correction), then sum results with field additions.
    match N {
        0 => PackedMontyField31Neon::<P>::ZERO,
        1 => lhs[0].into() * rhs[0].into(),
        2 => unsafe { dot_product_2(&[lhs[0], lhs[1]], &[rhs[0], rhs[1]]) },
        _ => {
            // Process pairs using dot_product_2 (amortizes 1 monty reduction over 2 products)
            let mut acc: PackedMontyField31Neon<P> = unsafe { dot_product_2(&[lhs[0], lhs[1]], &[rhs[0], rhs[1]]) };
            let mut i = 2;
            while i + 1 < N {
                acc += unsafe { dot_product_2(&[lhs[i], lhs[i + 1]], &[rhs[i], rhs[i + 1]]) };
                i += 2;
            }
            if i < N {
                acc += lhs[i].into() * rhs[i].into();
            }
            acc
        }
    }
}

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
            let lhs = PackedMontyField31Neon([a[0], a[1], a[2], a[3]]);

            let out = lhs * b;

            res.copy_from_slice(&out.0[..4]);
        }
        5 => {
            let lhs = PackedMontyField31Neon([a[0], a[1], a[2], a[3]]);

            let out = lhs * b;
            res[4] = a[4] * b;

            res[..4].copy_from_slice(&out.0[..4]);
        }
        8 => {
            let lhs_lo = PackedMontyField31Neon([a[0], a[1], a[2], a[3]]);
            let lhs_hi = PackedMontyField31Neon([a[4], a[5], a[6], a[7]]);

            let out_lo = lhs_lo * b;
            let out_hi = lhs_hi * b;

            res[..4].copy_from_slice(&out_lo.0);
            res[4..].copy_from_slice(&out_hi.0);
        }
        _ => panic!("Unsupported binomial extension degree: {}", WIDTH),
    }
}

/// Raise MontyField31 field elements to a small constant power `D`.
///
/// Currently, `D` must be one of 3, 5, or 7, if other powers are needed we can easily add them.
///
/// # Safety
/// Inputs must be signed 32-bit integers in the range `[-P, P]`.
/// Outputs will be unsigned 32-bit integers in canonical form `[0, P)`.
#[inline(always)]
#[must_use]
pub(crate) fn exp_small<PMP, const D: u64>(val: uint32x4_t) -> uint32x4_t
where
    PMP: PackedMontyParameters + FieldParameters,
{
    match D {
        3 => cube_unsigned::<PMP>(val),
        5 => exp_5_unsigned::<PMP>(val),
        7 => exp_7_unsigned::<PMP>(val),
        _ => panic!("No exp function for given D"),
    }
}
