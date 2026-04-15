// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use alloc::vec;
use alloc::vec::Vec;
use core::fmt::{Debug, Display, Formatter};
use core::hash::{Hash, Hasher};
use core::iter::{Product, Sum};
use core::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use core::{array, fmt};

use field::integers::QuotientMap;
use field::op_assign_macros::{impl_add_assign, impl_div_methods, impl_mul_methods, impl_sub_assign};
use field::{
    Field, InjectiveMonomial, Packable, PermutationMonomial, PrimeCharacteristicRing, PrimeField,
    PrimeField64, RawDataSerializable, TwoAdicField, impl_raw_serializable_primefield64,
    quotient_map_large_iint, quotient_map_large_uint, quotient_map_small_int,
};
use num_bigint::BigUint;
use rand::Rng;
use rand::distr::{Distribution, StandardUniform};
use serde::{Deserialize, Serialize};
use utils::{assume, branch_hint, flatten_to_base};

use crate::helpers::{exp_10540996611094048183, gcd_inner};

/// The Goldilocks prime.
pub(crate) const P: u64 = 0xFFFF_FFFF_0000_0001;

/// The prime field known as Goldilocks, defined as `F_p` where `p = 2^64 - 2^32 + 1`.
///
/// The internal representation is not necessarily canonical — any `u64` is allowed.
#[derive(Copy, Clone, Default, Serialize, Deserialize)]
#[repr(transparent)]
#[must_use]
pub struct Goldilocks {
    pub(crate) value: u64,
}

impl Goldilocks {
    /// Create a new field element from any `u64`.
    ///
    /// Any `u64` value is accepted. No reduction is performed since Goldilocks uses a
    /// non-canonical internal representation.
    #[inline]
    pub const fn new(value: u64) -> Self {
        Self { value }
    }

    /// Convert a `[u64; N]` array to an array of field elements.
    #[inline]
    pub const fn new_array<const N: usize>(input: [u64; N]) -> [Self; N] {
        let mut output = [Self::ZERO; N];
        let mut i = 0;
        while i < N {
            output[i].value = input[i];
            i += 1;
        }
        output
    }

    /// Convert a `[[u64; N]; M]` array to a 2D array of field elements.
    #[inline]
    pub const fn new_2d_array<const N: usize, const M: usize>(
        input: [[u64; N]; M],
    ) -> [[Self; N]; M] {
        let mut output = [[Self::ZERO; N]; M];
        let mut i = 0;
        while i < M {
            output[i] = Self::new_array(input[i]);
            i += 1;
        }
        output
    }

    /// Two's complement of `ORDER`, i.e. `2^64 - ORDER = 2^32 - 1`.
    const NEG_ORDER: u64 = Self::ORDER_U64.wrapping_neg();

    /// Generators of the two-adic subgroups: `TWO_ADIC_GENERATORS[0] = 1`,
    /// `TWO_ADIC_GENERATORS[i+1]^2 = TWO_ADIC_GENERATORS[i]`.
    pub const TWO_ADIC_GENERATORS: [Self; 33] = Self::new_array([
        0x0000000000000001,
        0xffffffff00000000,
        0x0001000000000000,
        0xfffffffeff000001,
        0xefffffff00000001,
        0x00003fffffffc000,
        0x0000008000000000,
        0xf80007ff08000001,
        0xbf79143ce60ca966,
        0x1905d02a5c411f4e,
        0x9d8f2ad78bfed972,
        0x0653b4801da1c8cf,
        0xf2c35199959dfcb6,
        0x1544ef2335d17997,
        0xe0ee099310bba1e2,
        0xf6b2cffe2306baac,
        0x54df9630bf79450e,
        0xabd0a6e8aa3d8a0e,
        0x81281a7b05f9beac,
        0xfbd41c6b8caa3302,
        0x30ba2ecd5e93e76d,
        0xf502aef532322654,
        0x4b2a18ade67246b5,
        0xea9d5a1336fbc98b,
        0x86cdcc31c307e171,
        0x4bbaf5976ecfefd8,
        0xed41d05b78d6e286,
        0x10d78dd8915a171d,
        0x59049500004a4485,
        0xdfa8c93ba46d2666,
        0x7e9bd009b86a0845,
        0x400a7f755588e659,
        0x185629dcda58878c,
    ]);

    /// Powers of two from 2^0 to 2^95 (inclusive).
    ///
    /// Note that `2^96 = -1 mod P`, so any power of two can be derived from this table.
    const POWERS_OF_TWO: [Self; 96] = {
        let mut powers_of_two = [Self::ONE; 96];
        let mut i = 1;
        while i < 64 {
            powers_of_two[i] = Self::new(1 << i);
            i += 1;
        }
        let mut var = Self::new(1 << 63);
        while i < 96 {
            var = const_add(var, var);
            powers_of_two[i] = var;
            i += 1;
        }
        powers_of_two
    };
}

impl PartialEq for Goldilocks {
    fn eq(&self, other: &Self) -> bool {
        self.as_canonical_u64() == other.as_canonical_u64()
    }
}

impl Eq for Goldilocks {}

impl Packable for Goldilocks {}

impl Hash for Goldilocks {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u64(self.as_canonical_u64());
    }
}

impl Ord for Goldilocks {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.as_canonical_u64().cmp(&other.as_canonical_u64())
    }
}

impl PartialOrd for Goldilocks {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Display for Goldilocks {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.as_canonical_u64(), f)
    }
}

impl Debug for Goldilocks {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Debug::fmt(&self.as_canonical_u64(), f)
    }
}

impl Distribution<Goldilocks> for StandardUniform {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Goldilocks {
        loop {
            let next_u64 = rng.next_u64();
            if next_u64 < Goldilocks::ORDER_U64 {
                return Goldilocks::new(next_u64);
            }
        }
    }
}

impl PrimeCharacteristicRing for Goldilocks {
    type PrimeSubfield = Self;

    const ZERO: Self = Self::new(0);
    const ONE: Self = Self::new(1);
    const TWO: Self = Self::new(2);
    const NEG_ONE: Self = Self::new(Self::ORDER_U64 - 1);

    #[inline]
    fn from_prime_subfield(f: Self::PrimeSubfield) -> Self {
        f
    }

    #[inline]
    fn from_bool(b: bool) -> Self {
        Self::new(b.into())
    }

    #[inline]
    fn halve(&self) -> Self {
        Self::new(crate::helpers::halve_u64::<P>(self.value))
    }

    #[inline]
    fn mul_2exp_u64(&self, exp: u64) -> Self {
        // 2^96 = -1 mod P, 2^192 = 1 mod P.
        if exp < 96 {
            *self * Self::POWERS_OF_TWO[exp as usize]
        } else if exp < 192 {
            -*self * Self::POWERS_OF_TWO[(exp - 96) as usize]
        } else {
            self.mul_2exp_u64(exp % 192)
        }
    }

    #[inline]
    fn div_2exp_u64(&self, mut exp: u64) -> Self {
        // 2^{-n} = 2^{192 - n} mod P.
        exp %= 192;
        self.mul_2exp_u64(192 - exp)
    }

    #[inline]
    fn sum_array<const N: usize>(input: &[Self]) -> Self {
        assert_eq!(N, input.len());
        match N {
            0 => Self::ZERO,
            1 => input[0],
            2 => input[0] + input[1],
            3 => input[0] + input[1] + input[2],
            _ => input.iter().copied().sum(),
        }
    }

    #[inline]
    fn dot_product<const N: usize>(lhs: &[Self; N], rhs: &[Self; N]) -> Self {
        // OFFSET has two key properties:
        //   1. it's a multiple of P,
        //   2. it exceeds the maximum sum of two u64 products.
        const OFFSET: u128 = ((P as u128) << 64) - (P as u128) + ((P as u128) << 32);
        const {
            assert!((N as u32) <= (1 << 31));
        }
        match N {
            0 => Self::ZERO,
            1 => lhs[0] * rhs[0],
            2 => {
                let long_prod_0 = (lhs[0].value as u128) * (rhs[0].value as u128);
                let long_prod_1 = (lhs[1].value as u128) * (rhs[1].value as u128);
                let (sum, over) = long_prod_0.overflowing_add(long_prod_1);
                let sum_corr = sum.wrapping_sub(OFFSET);
                if over {
                    reduce128(sum_corr)
                } else {
                    reduce128(sum)
                }
            }
            _ => {
                let (lo_plus_hi, hi) = lhs
                    .iter()
                    .zip(rhs)
                    .map(|(x, y)| (x.value as u128) * (y.value as u128))
                    .fold((0_u128, 0_u64), |(acc_lo, acc_hi), val| {
                        let val_hi = (val >> 96) as u64;
                        unsafe { (acc_lo.wrapping_add(val), acc_hi.unchecked_add(val_hi)) }
                    });
                let lo = lo_plus_hi.wrapping_sub((hi as u128) << 96);
                let sum = unsafe { lo.unchecked_add(P.unchecked_sub(hi) as u128) };
                reduce128(sum)
            }
        }
    }

    #[inline]
    fn zero_vec(len: usize) -> Vec<Self> {
        // SAFETY: `#[repr(transparent)]` means `Goldilocks` and `u64` share layout.
        unsafe { flatten_to_base(vec![0u64; len]) }
    }
}

/// `p - 1 = 2^32 * 3 * 5 * 17 * 257 * 65537`. The smallest `D` with `gcd(p - 1, D) = 1` is 7.
impl InjectiveMonomial<7> for Goldilocks {}

impl PermutationMonomial<7> for Goldilocks {
    fn injective_exp_root_n(&self) -> Self {
        exp_10540996611094048183(*self)
    }
}

impl RawDataSerializable for Goldilocks {
    impl_raw_serializable_primefield64!();
}

impl Field for Goldilocks {
    type Packing = Self;

    const GENERATOR: Self = Self::new(7);

    #[inline]
    fn is_zero(&self) -> bool {
        self.value == 0 || self.value == Self::ORDER_U64
    }

    fn try_inverse(&self) -> Option<Self> {
        if self.is_zero() {
            return None;
        }
        Some(gcd_inversion(*self))
    }

    #[inline]
    fn order() -> BigUint {
        P.into()
    }
}

quotient_map_small_int!(Goldilocks, u64, [u8, u16, u32]);
quotient_map_small_int!(Goldilocks, i64, [i8, i16, i32]);
quotient_map_large_uint!(
    Goldilocks,
    u64,
    Goldilocks::ORDER_U64,
    "`[0, 2^64 - 2^32]`",
    "`[0, 2^64 - 1]`",
    [u128]
);
quotient_map_large_iint!(
    Goldilocks,
    i64,
    "`[-(2^63 - 2^31), 2^63 - 2^31]`",
    "`[1 + 2^32 - 2^64, 2^64 - 1]`",
    [(i128, u128)]
);

impl QuotientMap<u64> for Goldilocks {
    #[inline]
    fn from_int(int: u64) -> Self {
        Self::new(int)
    }

    #[inline]
    fn from_canonical_checked(int: u64) -> Option<Self> {
        (int < Self::ORDER_U64).then(|| Self::new(int))
    }

    #[inline(always)]
    unsafe fn from_canonical_unchecked(int: u64) -> Self {
        Self::new(int)
    }
}

impl QuotientMap<i64> for Goldilocks {
    #[inline]
    fn from_int(int: i64) -> Self {
        if int >= 0 {
            Self::new(int as u64)
        } else {
            Self::new(Self::ORDER_U64.wrapping_add_signed(int))
        }
    }

    #[inline]
    fn from_canonical_checked(int: i64) -> Option<Self> {
        const POS_BOUND: i64 = (P >> 1) as i64;
        const NEG_BOUND: i64 = -POS_BOUND;
        match int {
            0..=POS_BOUND => Some(Self::new(int as u64)),
            NEG_BOUND..0 => Some(Self::new(Self::ORDER_U64.wrapping_add_signed(int))),
            _ => None,
        }
    }

    #[inline(always)]
    unsafe fn from_canonical_unchecked(int: i64) -> Self {
        Self::from_int(int)
    }
}

impl PrimeField for Goldilocks {
    fn as_canonical_biguint(&self) -> BigUint {
        self.as_canonical_u64().into()
    }
}

impl PrimeField64 for Goldilocks {
    const ORDER_U64: u64 = P;

    #[inline]
    fn as_canonical_u64(&self) -> u64 {
        let mut c = self.value;
        // Single conditional subtraction is sufficient since `2 * ORDER` would overflow u64.
        if c >= Self::ORDER_U64 {
            c -= Self::ORDER_U64;
        }
        c
    }
}

impl TwoAdicField for Goldilocks {
    const TWO_ADICITY: usize = 32;

    fn two_adic_generator(bits: usize) -> Self {
        assert!(bits <= Self::TWO_ADICITY);
        Self::TWO_ADIC_GENERATORS[bits]
    }
}

/// `const` version of addition — useful for building const tables.
#[inline]
const fn const_add(lhs: Goldilocks, rhs: Goldilocks) -> Goldilocks {
    let (sum, over) = lhs.value.overflowing_add(rhs.value);
    let (mut sum, over) = sum.overflowing_add((over as u64) * Goldilocks::NEG_ORDER);
    if over {
        sum += Goldilocks::NEG_ORDER;
    }
    Goldilocks::new(sum)
}

impl Add for Goldilocks {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self {
        let (sum, over) = self.value.overflowing_add(rhs.value);
        let (mut sum, over) = sum.overflowing_add(u64::from(over) * Self::NEG_ORDER);
        if over {
            unsafe {
                assume(self.value > Self::ORDER_U64 && rhs.value > Self::ORDER_U64);
            }
            branch_hint();
            sum += Self::NEG_ORDER;
        }
        Self::new(sum)
    }
}

impl Sub for Goldilocks {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Self) -> Self {
        let (diff, under) = self.value.overflowing_sub(rhs.value);
        let (mut diff, under) = diff.overflowing_sub(u64::from(under) * Self::NEG_ORDER);
        if under {
            unsafe {
                assume(self.value < Self::NEG_ORDER - 1 && rhs.value > Self::ORDER_U64);
            }
            branch_hint();
            diff -= Self::NEG_ORDER;
        }
        Self::new(diff)
    }
}

impl Neg for Goldilocks {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self::Output {
        Self::new(Self::ORDER_U64 - self.as_canonical_u64())
    }
}

impl Mul for Goldilocks {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> Self {
        reduce128(u128::from(self.value) * u128::from(rhs.value))
    }
}

impl_add_assign!(Goldilocks);
impl_sub_assign!(Goldilocks);
impl_mul_methods!(Goldilocks);
impl_div_methods!(Goldilocks, Goldilocks);

impl Sum for Goldilocks {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        // Faster than `reduce` for iterators of length > 2; cannot overflow provided len < 2^64.
        let sum = iter.map(|x| x.value as u128).sum::<u128>();
        reduce128(sum)
    }
}

/// Reduce to a 64-bit value. Output may be in `[0, 2^64)`, i.e. not necessarily canonical.
#[inline]
pub(crate) fn reduce128(x: u128) -> Goldilocks {
    let (x_lo, x_hi) = split(x);
    let x_hi_hi = x_hi >> 32;
    let x_hi_lo = x_hi & Goldilocks::NEG_ORDER;

    let (mut t0, borrow) = x_lo.overflowing_sub(x_hi_hi);
    if borrow {
        branch_hint();
        t0 -= Goldilocks::NEG_ORDER;
    }
    let t1 = x_hi_lo * Goldilocks::NEG_ORDER;
    let t2 = unsafe { add_no_canonicalize_trashing_input(t0, t1) };
    Goldilocks::new(t2)
}

#[inline]
#[allow(clippy::cast_possible_truncation)]
const fn split(x: u128) -> (u64, u64) {
    (x as u64, (x >> 64) as u64)
}

/// Fast addition modulo `ORDER` on x86-64, using CF/SBB to pick the adjustment branchlessly.
///
/// # Safety
/// - Only correct if `x + y < 2^64 + ORDER = 0x1_FFFF_FFFF_0000_0001`.
/// - Overwrites both inputs in registers on x86; avoid reusing them.
#[inline(always)]
#[cfg(target_arch = "x86_64")]
unsafe fn add_no_canonicalize_trashing_input(x: u64, y: u64) -> u64 {
    unsafe {
        let res_wrapped: u64;
        let adjustment: u64;
        core::arch::asm!(
            "add {0}, {1}",
            "sbb {1:e}, {1:e}",
            inlateout(reg) x => res_wrapped,
            inlateout(reg) y => adjustment,
            options(pure, nomem, nostack),
        );
        assume(x != 0 || (res_wrapped == y && adjustment == 0));
        assume(y != 0 || (res_wrapped == x && adjustment == 0));
        res_wrapped + adjustment
    }
}

#[inline(always)]
#[cfg(not(target_arch = "x86_64"))]
unsafe fn add_no_canonicalize_trashing_input(x: u64, y: u64) -> u64 {
    let (res_wrapped, carry) = x.overflowing_add(y);
    res_wrapped + Goldilocks::NEG_ORDER * u64::from(carry)
}

/// Binary-GCD inversion for Goldilocks.
///
/// Uses the "update factor" variant from https://eprint.iacr.org/2020/972.pdf: compute
/// factors off by a known power of two, then correct at the end via a linear combination.
fn gcd_inversion(input: Goldilocks) -> Goldilocks {
    let (mut a, mut b) = (input.value, P);

    // `len(a) + len(b) <= 128` initially; 126 iterations suffice to drive it to <= 2.
    // Split into 2 rounds of 63.
    const ROUND_SIZE: usize = 63;

    let (f00, _, f10, _) = gcd_inner::<ROUND_SIZE>(&mut a, &mut b);
    let (_, _, f11, g11) = gcd_inner::<ROUND_SIZE>(&mut a, &mut b);

    // The update factors are i64's, but we interpret `-2^63` as `2^63` because
    // `gcd_inner` outputs sit in `(-2^ROUND_SIZE, 2^ROUND_SIZE]`.
    let u = from_unusual_int(f00);
    let v = from_unusual_int(f10);
    let u_fac11 = from_unusual_int(f11);
    let v_fac11 = from_unusual_int(g11);

    // Each iteration introduced a factor of 2, so we need to divide by `2^126`.
    // `2^192 = 1 mod P`, so multiply by `2^66` instead (192 - 126 = 66).
    (u * u_fac11 + v * v_fac11).mul_2exp_u64(66)
}

/// Convert an `i64` to Goldilocks, interpreting `i64::MIN` as `2^63` (not `-2^63`).
const fn from_unusual_int(int: i64) -> Goldilocks {
    if (int >= 0) || (int == i64::MIN) {
        Goldilocks::new(int as u64)
    } else {
        Goldilocks::new(Goldilocks::ORDER_U64.wrapping_add_signed(int))
    }
}

// A few unused-variable suppression helpers that clippy might warn about
#[allow(dead_code)]
fn _unused_array_touch() {
    let _ = array::from_fn::<u8, 0, _>(|_| 0);
}
