// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

//! Degree-3 trinomial extension of Goldilocks, `F_p[X] / (X^3 - X - 1)`.
//!
//! Elements are `a_0 + a_1*X + a_2*X^2`. Reduction rule: `X^3 = X + 1`,
//! consequently `X^4 = X^2 + X`.

use alloc::format;
use alloc::string::ToString;
use alloc::vec::Vec;
use core::array;
use core::fmt::{self, Debug, Display, Formatter};
use core::iter::{Product, Sum};
use core::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use field::{
    Algebra, BasedVectorSpace, ExtensionField, Field, Packable, PackedFieldExtension, PackedValue,
    PrimeCharacteristicRing, RawDataSerializable, TwoAdicField, field_to_array,
};
use itertools::Itertools;
use num_bigint::BigUint;
use rand::distr::{Distribution, StandardUniform};
use rand::prelude::Rng;
use serde::{Deserialize, Serialize};
use utils::{as_base_slice, as_base_slice_mut, flatten_to_base, reconstitute_from_base};

use crate::Goldilocks;

/// Frobenius coefficients for `X^3 - X - 1` over Goldilocks.
///
/// `FROBENIUS_COEFFS[0]` is `X^p mod (X^3 - X - 1)`, `FROBENIUS_COEFFS[1]` is `X^{2p} mod …`.
///
/// Values verified by the companion `plonky3/goldilocks` code.
pub const FROBENIUS_COEFFS: [[Goldilocks; 3]; 2] = [
    [
        Goldilocks::new(10615703402128488253),
        Goldilocks::new(10050274602728160328),
        Goldilocks::new(11746561000929144102),
    ],
    [
        Goldilocks::new(6700183068485440220),
        Goldilocks::new(14531223735771536287),
        Goldilocks::new(8396469466686423992),
    ],
];

/// Generator of the multiplicative group of the cubic extension, as a coefficient triple.
const EXT_GENERATOR: [Goldilocks; 3] = [Goldilocks::new(2), Goldilocks::new(1), Goldilocks::new(0)];

/// Degree-3 trinomial extension of Goldilocks.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Serialize, Deserialize, PartialOrd, Ord)]
#[repr(transparent)]
#[must_use]
pub struct CubicExtensionFieldGL {
    #[serde(with = "utils::array_serialization")]
    pub(crate) value: [Goldilocks; 3],
}

impl CubicExtensionFieldGL {
    /// Construct from a coefficient triple `[a_0, a_1, a_2]`.
    #[inline]
    pub const fn new(value: [Goldilocks; 3]) -> Self {
        Self { value }
    }
}

impl Default for CubicExtensionFieldGL {
    fn default() -> Self {
        Self::new([Goldilocks::ZERO; 3])
    }
}

impl From<Goldilocks> for CubicExtensionFieldGL {
    fn from(x: Goldilocks) -> Self {
        Self::new(field_to_array(x))
    }
}

impl From<[Goldilocks; 3]> for CubicExtensionFieldGL {
    fn from(x: [Goldilocks; 3]) -> Self {
        Self::new(x)
    }
}

impl Packable for CubicExtensionFieldGL {}

impl BasedVectorSpace<Goldilocks> for CubicExtensionFieldGL {
    const DIMENSION: usize = 3;

    #[inline]
    fn as_basis_coefficients_slice(&self) -> &[Goldilocks] {
        &self.value
    }

    #[inline]
    fn from_basis_coefficients_fn<Fn: FnMut(usize) -> Goldilocks>(f: Fn) -> Self {
        Self::new(array::from_fn(f))
    }

    #[inline]
    fn from_basis_coefficients_iter<I: ExactSizeIterator<Item = Goldilocks>>(
        mut iter: I,
    ) -> Option<Self> {
        (iter.len() == 3).then(|| Self::new(array::from_fn(|_| iter.next().unwrap())))
    }

    #[inline]
    fn flatten_to_base(vec: Vec<Self>) -> Vec<Goldilocks> {
        // SAFETY: `Self` is `repr(transparent)` over `[Goldilocks; 3]`.
        unsafe { flatten_to_base::<Goldilocks, Self>(vec) }
    }

    #[inline]
    fn reconstitute_from_base(vec: Vec<Goldilocks>) -> Vec<Self> {
        // SAFETY: `Self` is `repr(transparent)` over `[Goldilocks; 3]`.
        unsafe { reconstitute_from_base::<Goldilocks, Self>(vec) }
    }
}

impl ExtensionField<Goldilocks> for CubicExtensionFieldGL {
    type ExtensionPacking = Self;

    #[inline]
    fn is_in_basefield(&self) -> bool {
        self.value[1].is_zero() && self.value[2].is_zero()
    }

    #[inline]
    fn as_base(&self) -> Option<Goldilocks> {
        <Self as ExtensionField<Goldilocks>>::is_in_basefield(self).then(|| self.value[0])
    }
}

impl CubicExtensionFieldGL {
    /// Apply the Frobenius `x -> x^p`.
    ///
    /// `φ(a) = a_0 + a_1 * X^p + a_2 * X^{2p}`, reduced with the stored coefficients.
    #[inline]
    pub fn frobenius(&self) -> Self {
        let a = &self.value;
        let fc = &FROBENIUS_COEFFS;
        let tail = [a[1], a[2]];
        let c0 = a[0] + Goldilocks::dot_product::<2>(&tail, &[fc[0][0], fc[1][0]]);
        let c1 = Goldilocks::dot_product::<2>(&tail, &[fc[0][1], fc[1][1]]);
        let c2 = Goldilocks::dot_product::<2>(&tail, &[fc[0][2], fc[1][2]]);
        Self::new([c0, c1, c2])
    }
}

impl PrimeCharacteristicRing for CubicExtensionFieldGL {
    type PrimeSubfield = <Goldilocks as PrimeCharacteristicRing>::PrimeSubfield;

    const ZERO: Self = Self::new([Goldilocks::ZERO; 3]);
    const ONE: Self = Self::new(field_to_array(Goldilocks::ONE));
    const TWO: Self = Self::new(field_to_array(Goldilocks::TWO));
    const NEG_ONE: Self = Self::new(field_to_array(Goldilocks::NEG_ONE));

    #[inline]
    fn from_prime_subfield(f: Self::PrimeSubfield) -> Self {
        <Goldilocks as PrimeCharacteristicRing>::from_prime_subfield(f).into()
    }

    #[inline]
    fn halve(&self) -> Self {
        Self::new(self.value.map(|x| x.halve()))
    }

    #[inline]
    fn square(&self) -> Self {
        let mut res = Self::default();
        cubic_square(&self.value, &mut res.value);
        res
    }

    #[inline]
    fn mul_2exp_u64(&self, exp: u64) -> Self {
        Self::new(self.value.map(|x| x.mul_2exp_u64(exp)))
    }

    #[inline]
    fn div_2exp_u64(&self, exp: u64) -> Self {
        Self::new(self.value.map(|x| x.div_2exp_u64(exp)))
    }

    #[inline]
    fn zero_vec(len: usize) -> Vec<Self> {
        // SAFETY: `repr(transparent)` over `[Goldilocks; 3]`.
        unsafe { reconstitute_from_base(Goldilocks::zero_vec(len * 3)) }
    }
}

impl Algebra<Goldilocks> for CubicExtensionFieldGL {}

impl RawDataSerializable for CubicExtensionFieldGL {
    const NUM_BYTES: usize = <Goldilocks as RawDataSerializable>::NUM_BYTES * 3;

    #[inline]
    fn into_bytes(self) -> impl IntoIterator<Item = u8> {
        self.value.into_iter().flat_map(|x| x.into_bytes())
    }

    #[inline]
    fn into_byte_stream(input: impl IntoIterator<Item = Self>) -> impl IntoIterator<Item = u8> {
        Goldilocks::into_byte_stream(input.into_iter().flat_map(|x| x.value))
    }

    #[inline]
    fn into_u32_stream(input: impl IntoIterator<Item = Self>) -> impl IntoIterator<Item = u32> {
        Goldilocks::into_u32_stream(input.into_iter().flat_map(|x| x.value))
    }

    #[inline]
    fn into_u64_stream(input: impl IntoIterator<Item = Self>) -> impl IntoIterator<Item = u64> {
        Goldilocks::into_u64_stream(input.into_iter().flat_map(|x| x.value))
    }

    #[inline]
    fn into_parallel_byte_streams<const N: usize>(
        input: impl IntoIterator<Item = [Self; N]>,
    ) -> impl IntoIterator<Item = [u8; N]> {
        Goldilocks::into_parallel_byte_streams(
            input
                .into_iter()
                .flat_map(|x| (0..3).map(move |i| array::from_fn(|j| x[j].value[i]))),
        )
    }

    #[inline]
    fn into_parallel_u32_streams<const N: usize>(
        input: impl IntoIterator<Item = [Self; N]>,
    ) -> impl IntoIterator<Item = [u32; N]> {
        Goldilocks::into_parallel_u32_streams(
            input
                .into_iter()
                .flat_map(|x| (0..3).map(move |i| array::from_fn(|j| x[j].value[i]))),
        )
    }

    #[inline]
    fn into_parallel_u64_streams<const N: usize>(
        input: impl IntoIterator<Item = [Self; N]>,
    ) -> impl IntoIterator<Item = [u64; N]> {
        Goldilocks::into_parallel_u64_streams(
            input
                .into_iter()
                .flat_map(|x| (0..3).map(move |i| array::from_fn(|j| x[j].value[i]))),
        )
    }
}

impl Field for CubicExtensionFieldGL {
    type Packing = Self;

    const GENERATOR: Self = Self::new(EXT_GENERATOR);

    fn try_inverse(&self) -> Option<Self> {
        if self.is_zero() {
            return None;
        }
        Some(cubic_inv(self))
    }

    #[inline]
    fn add_slices(slice_1: &mut [Self], slice_2: &[Self]) {
        // SAFETY: `repr(transparent)` + addition is base-linear.
        unsafe {
            let base_slice_1 = as_base_slice_mut(slice_1);
            let base_slice_2 = as_base_slice(slice_2);
            Goldilocks::add_slices(base_slice_1, base_slice_2);
        }
    }

    #[inline]
    fn order() -> BigUint {
        Goldilocks::order().pow(3)
    }
}

impl Display for CubicExtensionFieldGL {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if self.is_zero() {
            write!(f, "0")
        } else {
            let str = self
                .value
                .iter()
                .enumerate()
                .filter(|(_, x)| !x.is_zero())
                .map(|(i, x)| match (i, x.is_one()) {
                    (0, _) => format!("{x}"),
                    (1, true) => "X".to_string(),
                    (1, false) => format!("{x} X"),
                    (_, true) => format!("X^{i}"),
                    (_, false) => format!("{x} X^{i}"),
                })
                .join(" + ");
            write!(f, "{str}")
        }
    }
}

impl Neg for CubicExtensionFieldGL {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self {
        Self::new(self.value.map(Goldilocks::neg))
    }
}

impl Add for CubicExtensionFieldGL {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self {
        Self::new([
            self.value[0] + rhs.value[0],
            self.value[1] + rhs.value[1],
            self.value[2] + rhs.value[2],
        ])
    }
}

impl Add<Goldilocks> for CubicExtensionFieldGL {
    type Output = Self;

    #[inline]
    fn add(mut self, rhs: Goldilocks) -> Self {
        self.value[0] += rhs;
        self
    }
}

impl AddAssign for CubicExtensionFieldGL {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        for i in 0..3 {
            self.value[i] += rhs.value[i];
        }
    }
}

impl AddAssign<Goldilocks> for CubicExtensionFieldGL {
    #[inline]
    fn add_assign(&mut self, rhs: Goldilocks) {
        self.value[0] += rhs;
    }
}

impl Sum for CubicExtensionFieldGL {
    #[inline]
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|acc, x| acc + x).unwrap_or(Self::ZERO)
    }
}

impl Sub for CubicExtensionFieldGL {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Self) -> Self {
        Self::new([
            self.value[0] - rhs.value[0],
            self.value[1] - rhs.value[1],
            self.value[2] - rhs.value[2],
        ])
    }
}

impl Sub<Goldilocks> for CubicExtensionFieldGL {
    type Output = Self;

    #[inline]
    fn sub(mut self, rhs: Goldilocks) -> Self {
        self.value[0] -= rhs;
        self
    }
}

impl SubAssign for CubicExtensionFieldGL {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        for i in 0..3 {
            self.value[i] -= rhs.value[i];
        }
    }
}

impl SubAssign<Goldilocks> for CubicExtensionFieldGL {
    #[inline]
    fn sub_assign(&mut self, rhs: Goldilocks) {
        self.value[0] -= rhs;
    }
}

impl Mul for CubicExtensionFieldGL {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> Self {
        let mut res = Self::default();
        cubic_mul(&self.value, &rhs.value, &mut res.value);
        res
    }
}

impl Mul<Goldilocks> for CubicExtensionFieldGL {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Goldilocks) -> Self {
        Self::new([self.value[0] * rhs, self.value[1] * rhs, self.value[2] * rhs])
    }
}

impl MulAssign for CubicExtensionFieldGL {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl MulAssign<Goldilocks> for CubicExtensionFieldGL {
    #[inline]
    fn mul_assign(&mut self, rhs: Goldilocks) {
        *self = *self * rhs;
    }
}

impl Product for CubicExtensionFieldGL {
    #[inline]
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|acc, x| acc * x).unwrap_or(Self::ONE)
    }
}

impl Div for CubicExtensionFieldGL {
    type Output = Self;

    #[allow(clippy::suspicious_arithmetic_impl)]
    #[inline]
    fn div(self, rhs: Self) -> Self::Output {
        self * rhs.inverse()
    }
}

impl DivAssign for CubicExtensionFieldGL {
    #[inline]
    fn div_assign(&mut self, rhs: Self) {
        *self = *self / rhs;
    }
}

impl Distribution<CubicExtensionFieldGL> for StandardUniform {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> CubicExtensionFieldGL {
        CubicExtensionFieldGL::new(array::from_fn(|_| self.sample(rng)))
    }
}

impl TwoAdicField for CubicExtensionFieldGL {
    const TWO_ADICITY: usize = Goldilocks::TWO_ADICITY;

    #[inline]
    fn two_adic_generator(bits: usize) -> Self {
        Goldilocks::two_adic_generator(bits).into()
    }
}

// PackedFieldExtension: since Goldilocks has trivial packing (Packing = Self), the cubic
// extension is also its own packing.
impl PackedFieldExtension<Goldilocks, CubicExtensionFieldGL> for CubicExtensionFieldGL {
    #[inline]
    fn from_ext_slice(ext_slice: &[CubicExtensionFieldGL]) -> Self {
        // Goldilocks::Packing::WIDTH == 1, so the input is a single element.
        *CubicExtensionFieldGL::from_slice(ext_slice)
    }

    #[inline]
    fn packed_ext_powers(base: CubicExtensionFieldGL) -> field::Powers<Self> {
        // `Powers` is just an iterator over `base^k` starting at `k = 1`.
        use field::Powers;
        Powers {
            base,
            current: Self::ONE,
        }
    }
}

// ============================================================================
// Arithmetic kernels for `F_p[X] / (X^3 - X - 1)`.
// ============================================================================

/// Multiply two cubic extension elements.
///
/// Given `a = a_0 + a_1 X + a_2 X^2` and `b = b_0 + b_1 X + b_2 X^2`, compute the
/// product reduced by `X^3 - X - 1` (so `X^3 = X + 1`, `X^4 = X^2 + X`).
#[inline]
pub fn cubic_mul(a: &[Goldilocks; 3], b: &[Goldilocks; 3], res: &mut [Goldilocks; 3]) {
    let a0 = a[0];
    let a1 = a[1];
    let a2 = a[2];
    let b0 = b[0];
    let b1 = b[1];
    let b2 = b[2];

    let a1b2 = a1 * b2;
    let a2b1 = a2 * b1;
    let a2b2 = a2 * b2;

    // constant: a0 b0 + a1 b2 + a2 b1
    res[0] = a0 * b0 + a1b2 + a2b1;
    // linear: a0 b1 + a1 b0 + a1 b2 + a2 b1 + a2 b2
    res[1] = a0 * b1 + a1 * b0 + a1b2 + a2b1 + a2b2;
    // quadratic: a0 b2 + a1 b1 + a2 b0 + a2 b2
    res[2] = a0 * b2 + a1 * b1 + a2 * b0 + a2b2;
}

/// Square a cubic extension element (same reduction rule as `cubic_mul`).
#[inline]
pub fn cubic_square(a: &[Goldilocks; 3], res: &mut [Goldilocks; 3]) {
    let a0 = a[0];
    let a1 = a[1];
    let a2 = a[2];

    let a0_sq = a0.square();
    let a1_sq = a1.square();
    let a2_sq = a2.square();
    let two_a0_a1 = (a0 * a1).double();
    let two_a0_a2 = (a0 * a2).double();
    let two_a1_a2 = (a1 * a2).double();

    // constant: a0^2 + 2 a1 a2
    res[0] = a0_sq + two_a1_a2;
    // linear: 2 a0 a1 + 2 a1 a2 + a2^2
    res[1] = two_a0_a1 + two_a1_a2 + a2_sq;
    // quadratic: 2 a0 a2 + a1^2 + a2^2
    res[2] = two_a0_a2 + a1_sq + a2_sq;
}

/// Invert a cubic extension element via adjugate/determinant — no Frobenius round trip needed.
///
/// The multiplication-by-`a` matrix (in the basis `{1, X, X^2}`, using `X^3 = X + 1`) is
///
/// ```text
/// M = | a0    a2      a1      |
///     | a1    a0 + a2 a1 + a2 |
///     | a2    a1      a0 + a2 |
/// ```
///
/// so `a^{-1} = adj(M) · e_0 / det(M)`.
#[inline]
fn cubic_inv(a: &CubicExtensionFieldGL) -> CubicExtensionFieldGL {
    let [a0, a1, a2] = a.value;

    let a0_sq = a0.square();
    let a1_sq = a1.square();
    let a2_sq = a2.square();
    let a0a1 = a0 * a1;
    let a0a2 = a0 * a2;
    let a1a2 = a1 * a2;

    // Cofactors of the first row of `M` (see matrix above):
    //   n0 = a1 a2 + a1^2 - a0^2 - 2 a0 a2 - a2^2
    let n0 = a1a2 + a1_sq - a0_sq - a0a2.double() - a2_sq;
    //   n1 = a0 a1 - a2^2
    let n1 = a0a1 - a2_sq;
    //   n2 = a0 a2 + a2^2 - a1^2
    let n2 = a0a2 + a2_sq - a1_sq;

    // `t = -det(M) = a0 n0 + a2 n1 + a1 n2`.
    let t = a0 * n0 + a2 * n1 + a1 * n2;
    let t_inv = t.inverse();

    CubicExtensionFieldGL::new([n0 * t_inv, n1 * t_inv, n2 * t_inv])
}

// ============================================================================
// Frobenius sanity test — exercised during `cargo test`.
// ============================================================================

#[cfg(test)]
mod tests {
    use field::{Field, PrimeCharacteristicRing, PrimeField64};
    use rand::rngs::StdRng;
    use rand::{RngExt, SeedableRng};

    use super::*;

    #[test]
    fn inverse_roundtrip() {
        let mut rng = StdRng::seed_from_u64(1);
        for _ in 0..32 {
            let a: CubicExtensionFieldGL = rng.random();
            if a.is_zero() {
                continue;
            }
            let a_inv = a.inverse();
            assert_eq!(a * a_inv, CubicExtensionFieldGL::ONE);
        }
    }

    #[test]
    fn x_cubed_equals_x_plus_one() {
        // The extension is `F_p[X]/(X^3 - X - 1)`, so `X^3 = X + 1`.
        let x = CubicExtensionFieldGL::new([Goldilocks::ZERO, Goldilocks::ONE, Goldilocks::ZERO]);
        let x_cubed = x * x * x;
        let expected = CubicExtensionFieldGL::new([Goldilocks::ONE, Goldilocks::ONE, Goldilocks::ZERO]);
        assert_eq!(x_cubed, expected);
    }

    #[test]
    fn frobenius_matches_pth_power() {
        let mut rng = StdRng::seed_from_u64(2);
        for _ in 0..8 {
            let a: CubicExtensionFieldGL = rng.random();
            let a_frob = a.frobenius();
            let a_pth = a.exp_u64(Goldilocks::ORDER_U64);
            assert_eq!(a_frob, a_pth);
        }
    }
}
