// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use alloc::vec::Vec;
use core::arch::aarch64::{
    uint64x2_t, vaddq_u64, vandq_u64, vdupq_n_u64, vgetq_lane_u64, vsetq_lane_u64, vshrq_n_u64, vsubq_u64,
};
use core::fmt::Debug;
use core::iter::{Product, Sum};
use core::mem::transmute;
use core::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use field::op_assign_macros::{
    impl_add_assign, impl_add_base_field, impl_div_methods, impl_mul_base_field, impl_mul_methods, impl_packed_value,
    impl_rng, impl_sub_assign, impl_sub_base_field, impl_sum_prod_base_field, ring_sum,
};
use field::{
    Algebra, Field, InjectiveMonomial, PackedField, PackedFieldPow2, PackedValue, PermutationMonomial,
    PrimeCharacteristicRing, PrimeField64,
};
use rand::Rng;
use rand::distr::{Distribution, StandardUniform};
use utils::reconstitute_from_base;

use crate::helpers::exp_10540996611094048183;
use crate::{Goldilocks, P};

const WIDTH: usize = 2;

/// Equal to `2^32 - 1 = 2^64 mod P`.
const EPSILON: u64 = Goldilocks::ORDER_U64.wrapping_neg();

/// Hand-scheduled inline-asm variant tuned for the **scalar / single-lane Mul**
/// path on aarch64. Saves one ALU op vs the LLVM-emitted form by collapsing `lsr+subs` into the
/// shifted-register `subs xT, lo, hi, lsr #32` form.
#[inline(always)]
pub(super) fn mul_reduce_asm(a: u64, b: u64) -> u64 {
    let result: u64;
    // SAFETY: integer ALU only; `pure, nomem, nostack` lets LLVM schedule, CSE, DCE.
    unsafe {
        core::arch::asm!(
            "mul     {lo},        {a},  {b}",
            "umulh   {hi},        {a},  {b}",
            "subs    {tmp},       {lo}, {hi}, lsr #32",
            "csel    {corr1},     {p},  xzr,  lo",
            "add     {tmp},       {corr1}, {tmp}",
            "lsl     {hi_lo_eps}, {hi}, #32",
            "sub     {hi_lo_eps}, {hi_lo_eps}, {hi:w}, uxtw",
            "adds    {res},       {tmp}, {hi_lo_eps}",
            "csel    {corr2},     {eps}, xzr,  hs",
            "add     {result},    {corr2}, {res}",
            a = in(reg) a,
            b = in(reg) b,
            lo = out(reg) _,
            hi = out(reg) _,
            tmp = out(reg) _,
            corr1 = out(reg) _,
            hi_lo_eps = out(reg) _,
            res = out(reg) _,
            corr2 = out(reg) _,
            result = lateout(reg) result,
            p = in(reg) Goldilocks::ORDER_U64,
            eps = in(reg) EPSILON,
            options(pure, nomem, nostack),
        );
    }
    result
}

/// Vectorized NEON implementation of `Goldilocks` arithmetic.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
#[repr(transparent)]
#[must_use]
pub struct PackedGoldilocksNeon(pub [Goldilocks; WIDTH]);

impl PackedGoldilocksNeon {
    #[inline]
    #[must_use]
    pub(crate) fn to_vector(self) -> uint64x2_t {
        unsafe { transmute(self) }
    }

    #[inline]
    pub(crate) fn from_vector(vector: uint64x2_t) -> Self {
        unsafe { transmute(vector) }
    }

    #[inline]
    const fn broadcast(value: Goldilocks) -> Self {
        Self([value; WIDTH])
    }
}

impl From<Goldilocks> for PackedGoldilocksNeon {
    fn from(x: Goldilocks) -> Self {
        Self::broadcast(x)
    }
}

// Add/Sub/Neg are emulated as two independent scalar Goldilocks ops. On Apple Silicon's wide
// scalar pipeline, two pipelined scalar adds beat the NEON modular-reduction sequence (XOR-shift
// + signed compare + conditional add) per element. Storage stays as `[Goldilocks; 2]` (16 bytes)
// so the compiler keeps elements in either GPRs or NEON regs as needed; only `mul`/`square` use
// the dual-lane interleaved ASM.
impl Add for PackedGoldilocksNeon {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        Self([self.0[0] + rhs.0[0], self.0[1] + rhs.0[1]])
    }
}

impl Sub for PackedGoldilocksNeon {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Self) -> Self {
        Self([self.0[0] - rhs.0[0], self.0[1] - rhs.0[1]])
    }
}

impl Neg for PackedGoldilocksNeon {
    type Output = Self;
    #[inline]
    fn neg(self) -> Self {
        Self([-self.0[0], -self.0[1]])
    }
}

impl Mul for PackedGoldilocksNeon {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        // Hand-scheduled `mul_reduce_asm` saves one ALU op per lane vs LLVM's pure-Rust form.
        Self([
            Goldilocks::new(mul_reduce_asm(self.0[0].value, rhs.0[0].value)),
            Goldilocks::new(mul_reduce_asm(self.0[1].value, rhs.0[1].value)),
        ])
    }
}

impl_add_assign!(PackedGoldilocksNeon);
impl_sub_assign!(PackedGoldilocksNeon);
impl_mul_methods!(PackedGoldilocksNeon);
ring_sum!(PackedGoldilocksNeon);
impl_rng!(PackedGoldilocksNeon);

impl PrimeCharacteristicRing for PackedGoldilocksNeon {
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
    fn dot_product<const N: usize>(lhs: &[Self; N], rhs: &[Self; N]) -> Self {
        Self::from_fn(|lane| {
            let lhs_lane: [Goldilocks; N] = core::array::from_fn(|i| lhs[i].as_slice()[lane]);
            let rhs_lane: [Goldilocks; N] = core::array::from_fn(|i| rhs[i].as_slice()[lane]);
            Goldilocks::dot_product(&lhs_lane, &rhs_lane)
        })
    }

    #[inline]
    fn square(&self) -> Self {
        // Same rationale as `Mul`: scalar reduction avoids NEON<->GPR moves.
        let x0 = self.0[0].value;
        let x1 = self.0[1].value;
        Self([
            Goldilocks::new(mul_reduce_asm(x0, x0)),
            Goldilocks::new(mul_reduce_asm(x1, x1)),
        ])
    }

    #[inline]
    fn zero_vec(len: usize) -> Vec<Self> {
        unsafe { reconstitute_from_base(Goldilocks::zero_vec(len * WIDTH)) }
    }
}

impl InjectiveMonomial<7> for PackedGoldilocksNeon {}

impl PermutationMonomial<7> for PackedGoldilocksNeon {
    fn injective_exp_root_n(&self) -> Self {
        exp_10540996611094048183(*self)
    }
}

impl_add_base_field!(PackedGoldilocksNeon, Goldilocks);
impl_sub_base_field!(PackedGoldilocksNeon, Goldilocks);
impl_mul_base_field!(PackedGoldilocksNeon, Goldilocks);
impl_div_methods!(PackedGoldilocksNeon, Goldilocks);
impl_sum_prod_base_field!(PackedGoldilocksNeon, Goldilocks);

impl Algebra<Goldilocks> for PackedGoldilocksNeon {}

impl_packed_value!(PackedGoldilocksNeon, Goldilocks, WIDTH);

unsafe impl PackedField for PackedGoldilocksNeon {
    type Scalar = Goldilocks;
}

/// Interleave two 64-bit vectors at the element level.
/// For block_len=1: `[a0, a1]` x `[b0, b1]` -> `[a0, b0]`, `[a1, b1]`.
#[inline]
pub fn interleave_u64(v0: uint64x2_t, v1: uint64x2_t) -> (uint64x2_t, uint64x2_t) {
    unsafe {
        let a0 = vgetq_lane_u64::<0>(v0);
        let a1 = vgetq_lane_u64::<1>(v0);
        let b0 = vgetq_lane_u64::<0>(v1);
        let b1 = vgetq_lane_u64::<1>(v1);

        let r0 = vsetq_lane_u64::<1>(b0, vsetq_lane_u64::<0>(a0, vdupq_n_u64(0)));
        let r1 = vsetq_lane_u64::<1>(b1, vsetq_lane_u64::<0>(a1, vdupq_n_u64(0)));

        (r0, r1)
    }
}

unsafe impl PackedFieldPow2 for PackedGoldilocksNeon {
    fn interleave(&self, other: Self, block_len: usize) -> (Self, Self) {
        let (v0, v1) = (self.to_vector(), other.to_vector());
        let (res0, res1) = match block_len {
            1 => interleave_u64(v0, v1),
            2 => (v0, v1),
            _ => panic!("unsupported block length"),
        };
        (Self::from_vector(res0), Self::from_vector(res1))
    }
}

/// Halve a vector of Goldilocks field elements.
#[inline(always)]
pub(crate) fn halve(input: uint64x2_t) -> uint64x2_t {
    unsafe {
        let one = vdupq_n_u64(1);
        let zero = vdupq_n_u64(0);
        let half = vdupq_n_u64(P.div_ceil(2));

        let least_bit = vandq_u64(input, one);
        let t = vshrq_n_u64::<1>(input);
        // neg_least_bit is 0 or -1 (all bits 1).
        let neg_least_bit = vsubq_u64(zero, least_bit);
        let maybe_half = vandq_u64(half, neg_least_bit);
        vaddq_u64(t, maybe_half)
    }
}

#[cfg(test)]
mod tests {
    use super::{Goldilocks, PackedGoldilocksNeon, WIDTH};

    const SPECIAL_VALS: [Goldilocks; WIDTH] = Goldilocks::new_array([0xFFFF_FFFF_0000_0000, 0xFFFF_FFFF_FFFF_FFFF]);

    #[test]
    fn pack_round_trip() {
        let p = PackedGoldilocksNeon(SPECIAL_VALS);
        let v = p.to_vector();
        assert_eq!(PackedGoldilocksNeon::from_vector(v).0, SPECIAL_VALS);
    }
}
