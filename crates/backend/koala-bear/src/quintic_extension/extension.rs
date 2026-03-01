// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use alloc::format;
use alloc::string::ToString;
use alloc::vec::Vec;
use core::array;
use core::fmt::{self, Debug, Display, Formatter};
use core::iter::{Product, Sum};
use core::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use field::{
    Algebra, BasedVectorSpace, ExtensionField, Field, Packable, PrimeCharacteristicRing, RawDataSerializable,
    TwoAdicField, field_to_array,
};
use itertools::Itertools;
use num_bigint::BigUint;
use rand::distr::StandardUniform;
use rand::prelude::Distribution;
use serde::{Deserialize, Serialize};
use utils::{as_base_slice, as_base_slice_mut, flatten_to_base, reconstitute_from_base};

use super::packed_extension::PackedQuinticExtensionField;
use crate::QuinticExtendable;

/// Quintic Extension Field (degree 5), specifically designed for Koala-Bear
/// Irreducible polynomial: X^5 + X^2 - 1
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Serialize, Deserialize, PartialOrd, Ord)]
#[repr(transparent)] // Needed to make various casts safe.
#[must_use]
pub struct QuinticExtensionField<F> {
    #[serde(
        with = "utils::array_serialization",
        bound(serialize = "F: Serialize", deserialize = "F: Deserialize<'de>")
    )]
    pub(crate) value: [F; 5],
}

impl<F> QuinticExtensionField<F> {
    pub(crate) const fn new(value: [F; 5]) -> Self {
        Self { value }
    }
}

impl<F: Field> Default for QuinticExtensionField<F> {
    fn default() -> Self {
        Self::new(array::from_fn(|_| F::ZERO))
    }
}

impl<F: Field> From<F> for QuinticExtensionField<F> {
    fn from(x: F) -> Self {
        Self::new(field_to_array(x))
    }
}

impl<F: QuinticExtendable> Packable for QuinticExtensionField<F> {}

impl<F: QuinticExtendable> BasedVectorSpace<F> for QuinticExtensionField<F> {
    const DIMENSION: usize = 5;

    #[inline]
    fn as_basis_coefficients_slice(&self) -> &[F] {
        &self.value
    }

    #[inline]
    fn from_basis_coefficients_fn<Fn: FnMut(usize) -> F>(f: Fn) -> Self {
        Self::new(array::from_fn(f))
    }

    #[inline]
    fn from_basis_coefficients_iter<I: ExactSizeIterator<Item = F>>(mut iter: I) -> Option<Self> {
        (iter.len() == 5).then(|| Self::new(array::from_fn(|_| iter.next().unwrap()))) // The unwrap is safe as we just checked the length of iter.
    }

    #[inline]
    fn flatten_to_base(vec: Vec<Self>) -> Vec<F> {
        unsafe {
            // Safety:
            // As `Self` is a `repr(transparent)`, it is stored identically in memory to `[A; 5]`
            flatten_to_base::<F, Self>(vec)
        }
    }

    #[inline]
    fn reconstitute_from_base(vec: Vec<F>) -> Vec<Self> {
        unsafe {
            // Safety:
            // As `Self` is a `repr(transparent)`, it is stored identically in memory to `[A; 5]`
            reconstitute_from_base::<F, Self>(vec)
        }
    }
}

impl<F: QuinticExtendable> ExtensionField<F> for QuinticExtensionField<F> {
    type ExtensionPacking = PackedQuinticExtensionField<F, F::Packing>;

    #[inline]
    fn is_in_basefield(&self) -> bool {
        self.value[1..].iter().all(F::is_zero)
    }

    #[inline]
    fn as_base(&self) -> Option<F> {
        <Self as ExtensionField<F>>::is_in_basefield(self).then(|| self.value[0])
    }
}

impl<F: QuinticExtendable> QuinticExtensionField<F> {
    #[inline]
    fn frobenius(&self) -> Self {
        let mut res = Self::ZERO;
        res.value[0] = self.value[0];
        for i in 0..4 {
            for j in 0..5 {
                res.value[j] += self.value[i + 1] * F::FROBENIUS_MATRIX[i][j];
            }
        }

        res
    }

    #[inline]
    fn repeated_frobenius(&self, count: usize) -> Self {
        if count == 0 {
            return *self;
        } else if count >= 5 {
            return self.repeated_frobenius(count % 5);
        }

        let mut res = self.frobenius();
        for _ in 1..count {
            res = res.frobenius();
        }
        res
    }
}

impl<F> PrimeCharacteristicRing for QuinticExtensionField<F>
where
    F: QuinticExtendable,
{
    type PrimeSubfield = <F as PrimeCharacteristicRing>::PrimeSubfield;

    const ZERO: Self = Self::new([F::ZERO; 5]);

    const ONE: Self = Self::new(field_to_array(F::ONE));

    const TWO: Self = Self::new(field_to_array(F::TWO));

    const NEG_ONE: Self = Self::new(field_to_array(F::NEG_ONE));

    const INVERSE_OF_TWO: Self = Self::new(field_to_array(F::INVERSE_OF_TWO));

    #[inline]
    fn from_prime_subfield(f: Self::PrimeSubfield) -> Self {
        <F as PrimeCharacteristicRing>::from_prime_subfield(f).into()
    }

    #[inline]
    fn halve(&self) -> Self {
        Self::new(self.value.map(|x| x.halve()))
    }

    #[inline(always)]
    fn square(&self) -> Self {
        let mut res = Self::default();
        quintic_square(&self.value, &mut res.value);
        res
    }

    #[inline]
    fn mul_2exp_u64(&self, exp: u64) -> Self {
        // Depending on the field, this might be a little slower than
        // the default implementation if the compiler doesn't realize `F::TWO.exp_u64(exp)` is a constant.
        Self::new(self.value.map(|x| x.mul_2exp_u64(exp)))
    }

    #[inline]
    fn div_2exp_u64(&self, exp: u64) -> Self {
        // Depending on the field, this might be a little slower than
        // the default implementation if the compiler doesn't realize `F::ONE.halve().exp_u64(exp)` is a constant.
        Self::new(self.value.map(|x| x.div_2exp_u64(exp)))
    }

    #[inline]
    fn zero_vec(len: usize) -> Vec<Self> {
        // SAFETY: this is a repr(transparent) wrapper around an array.
        unsafe { reconstitute_from_base(F::zero_vec(len * 5)) }
    }
}

impl<F: QuinticExtendable> Algebra<F> for QuinticExtensionField<F> {}

impl<F: QuinticExtendable> RawDataSerializable for QuinticExtensionField<F> {
    const NUM_BYTES: usize = F::NUM_BYTES * 5;

    #[inline]
    fn into_bytes(self) -> impl IntoIterator<Item = u8> {
        self.value.into_iter().flat_map(|x| x.into_bytes())
    }

    #[inline]
    fn into_byte_stream(input: impl IntoIterator<Item = Self>) -> impl IntoIterator<Item = u8> {
        F::into_byte_stream(input.into_iter().flat_map(|x| x.value))
    }

    #[inline]
    fn into_u32_stream(input: impl IntoIterator<Item = Self>) -> impl IntoIterator<Item = u32> {
        F::into_u32_stream(input.into_iter().flat_map(|x| x.value))
    }

    #[inline]
    fn into_u64_stream(input: impl IntoIterator<Item = Self>) -> impl IntoIterator<Item = u64> {
        F::into_u64_stream(input.into_iter().flat_map(|x| x.value))
    }

    #[inline]
    fn into_parallel_byte_streams<const N: usize>(
        input: impl IntoIterator<Item = [Self; N]>,
    ) -> impl IntoIterator<Item = [u8; N]> {
        F::into_parallel_byte_streams(
            input
                .into_iter()
                .flat_map(|x| (0..5).map(move |i| array::from_fn(|j| x[j].value[i]))),
        )
    }

    #[inline]
    fn into_parallel_u32_streams<const N: usize>(
        input: impl IntoIterator<Item = [Self; N]>,
    ) -> impl IntoIterator<Item = [u32; N]> {
        F::into_parallel_u32_streams(
            input
                .into_iter()
                .flat_map(|x| (0..5).map(move |i| array::from_fn(|j| x[j].value[i]))),
        )
    }

    #[inline]
    fn into_parallel_u64_streams<const N: usize>(
        input: impl IntoIterator<Item = [Self; N]>,
    ) -> impl IntoIterator<Item = [u64; N]> {
        F::into_parallel_u64_streams(
            input
                .into_iter()
                .flat_map(|x| (0..5).map(move |i| array::from_fn(|j| x[j].value[i]))),
        )
    }
}

impl<F: QuinticExtendable> Field for QuinticExtensionField<F> {
    type Packing = Self;

    const GENERATOR: Self = Self::new(F::EXT_GENERATOR);

    fn try_inverse(&self) -> Option<Self> {
        if self.is_zero() {
            return None;
        }

        Some(quintic_inv(self))
    }

    #[inline]
    fn add_slices(slice_1: &mut [Self], slice_2: &[Self]) {
        // By construction, Self is repr(transparent) over [F; D].
        // Additionally, addition is F-linear. Hence we can cast
        // everything to F and use F's add_slices.
        unsafe {
            let base_slice_1 = as_base_slice_mut(slice_1);
            let base_slice_2 = as_base_slice(slice_2);

            F::add_slices(base_slice_1, base_slice_2);
        }
    }

    #[inline]
    fn order() -> BigUint {
        F::order().pow(5)
    }
}

impl<F> Display for QuinticExtensionField<F>
where
    F: QuinticExtendable,
{
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

impl<F> Neg for QuinticExtensionField<F>
where
    F: QuinticExtendable,
{
    type Output = Self;

    #[inline]
    fn neg(self) -> Self {
        Self::new(self.value.map(F::neg))
    }
}

impl<F> Add for QuinticExtensionField<F>
where
    F: QuinticExtendable,
{
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self {
        let value = F::quintic_add(&self.value, &rhs.value);
        Self::new(value)
    }
}

impl<F> Add<F> for QuinticExtensionField<F>
where
    F: QuinticExtendable,
{
    type Output = Self;

    #[inline]
    fn add(mut self, rhs: F) -> Self {
        self.value[0] += rhs;
        self
    }
}

impl<F> AddAssign for QuinticExtensionField<F>
where
    F: QuinticExtendable,
{
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        for i in 0..5 {
            self.value[i] += rhs.value[i];
        }
    }
}

impl<F> AddAssign<F> for QuinticExtensionField<F>
where
    F: QuinticExtendable,
{
    #[inline]
    fn add_assign(&mut self, rhs: F) {
        self.value[0] += rhs;
    }
}

impl<F> Sum for QuinticExtensionField<F>
where
    F: QuinticExtendable,
{
    #[inline]
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|acc, x| acc + x).unwrap_or(Self::ZERO)
    }
}

impl<F> Sub for QuinticExtensionField<F>
where
    F: QuinticExtendable,
{
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Self) -> Self {
        let value = F::quintic_sub(&self.value, &rhs.value);
        Self::new(value)
    }
}

impl<F> Sub<F> for QuinticExtensionField<F>
where
    F: QuinticExtendable,
{
    type Output = Self;

    #[inline]
    fn sub(self, rhs: F) -> Self {
        let mut res = self.value;
        res[0] -= rhs;
        Self::new(res)
    }
}

impl<F> SubAssign for QuinticExtensionField<F>
where
    F: QuinticExtendable,
{
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        for i in 0..5 {
            self.value[i] -= rhs.value[i];
        }
    }
}

impl<F> SubAssign<F> for QuinticExtensionField<F>
where
    F: QuinticExtendable,
{
    #[inline]
    fn sub_assign(&mut self, rhs: F) {
        self.value[0] -= rhs;
    }
}

impl<F> Mul for QuinticExtensionField<F>
where
    F: QuinticExtendable,
{
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> Self {
        let a = self.value;
        let b = rhs.value;
        let mut res = Self::default();

        F::quintic_mul(&a, &b, &mut res.value);

        res
    }
}

impl<F> Mul<F> for QuinticExtensionField<F>
where
    F: QuinticExtendable,
{
    type Output = Self;

    #[inline]
    fn mul(self, rhs: F) -> Self {
        Self::new(F::quintic_base_mul(self.value, rhs))
    }
}

impl<F> MulAssign for QuinticExtensionField<F>
where
    F: QuinticExtendable,
{
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl<F> MulAssign<F> for QuinticExtensionField<F>
where
    F: QuinticExtendable,
{
    #[inline]
    fn mul_assign(&mut self, rhs: F) {
        *self = *self * rhs;
    }
}

impl<F> Product for QuinticExtensionField<F>
where
    F: QuinticExtendable,
{
    #[inline]
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|acc, x| acc * x).unwrap_or(Self::ONE)
    }
}

impl<F> Div for QuinticExtensionField<F>
where
    F: QuinticExtendable,
{
    type Output = Self;

    #[allow(clippy::suspicious_arithmetic_impl)]
    #[inline]
    fn div(self, rhs: Self) -> Self::Output {
        self * rhs.inverse()
    }
}

impl<F> DivAssign for QuinticExtensionField<F>
where
    F: QuinticExtendable,
{
    #[inline]
    fn div_assign(&mut self, rhs: Self) {
        *self = *self / rhs;
    }
}

impl<F: QuinticExtendable> Distribution<QuinticExtensionField<F>> for StandardUniform
where
    Self: Distribution<F>,
{
    #[inline]
    fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> QuinticExtensionField<F> {
        QuinticExtensionField::new(array::from_fn(|_| self.sample(rng)))
    }
}

impl<F: TwoAdicField + QuinticExtendable> TwoAdicField for QuinticExtensionField<F> {
    const TWO_ADICITY: usize = F::TWO_ADICITY;

    #[inline]
    fn two_adic_generator(bits: usize) -> Self {
        F::two_adic_generator(bits).into()
    }
}

/// Quintic extension field multiplication in F[X]/(X^5 + X^2 - 1).
#[inline]
pub fn quintic_mul<T: Copy + Sub<Output = T>>(
    a: &[T; 5],
    b: &[T; 5],
    dot_product: impl Fn(&[T; 5], &[T; 5]) -> T,
) -> [T; 5] {
    let b_0_m3 = b[0] - b[3];
    let b_1_m4 = b[1] - b[4];
    let b_4_m2 = b[4] - b[2];

    [
        dot_product(a, &[b[0], b[4], b[3], b[2], b_1_m4]),
        dot_product(a, &[b[1], b[0], b[4], b[3], b[2]]),
        dot_product(a, &[b[2], b_1_m4, b_0_m3, b_4_m2, b[3] - b_1_m4]),
        dot_product(a, &[b[3], b[2], b_1_m4, b_0_m3, b_4_m2]),
        dot_product(a, &[b[4], b[3], b[2], b_1_m4, b_0_m3]),
    ]
}

#[inline]
pub(crate) fn quintic_square<F, R>(a: &[R; 5], res: &mut [R; 5])
where
    F: Field,
    R: Algebra<F>,
{
    let two_a0 = a[0].double();
    let two_a1 = a[1].double();
    let two_a2 = a[2].double();
    let two_a3 = a[3].double();

    let two_a1_a4 = two_a1 * a[4];
    let two_a2_a3 = two_a2 * a[3];
    let two_a2_a4 = two_a2 * a[4];
    let two_a3_a4 = two_a3 * a[4];

    let a3_square = a[3].square();
    let a4_square = a[4].square();

    // Constant term = a0^2 + 2*a1*a4 + 2*a2*a3 - a4^2
    res[0] = R::dot_product(&[a[0], two_a1], &[a[0], a[4]]) + two_a2_a3 - a4_square;

    // Linear term = 2*a0*a1 + a3^2 + 2*a2*a4
    res[1] = two_a0 * a[1] + a3_square + two_a2_a4;

    // Square term = a1^2 + 2*a0*a2 - 2*a1*a4 - 2*a2*a3 + 2*a3*a4 + a4^2
    res[2] = a[1].square() + two_a0 * a[2] - two_a1_a4 - two_a2_a3 + two_a3_a4 + a4_square;

    // Cubic term = 2*a0*a3 + 2*a1*a2 - a3^2 - 2*a2*a4 + a4^2
    res[3] = R::dot_product(&[two_a0, two_a1], &[a[3], a[2]]) - a3_square - two_a2_a4 + a4_square;

    // Quartic term = a2^2 + 2*a0*a4 + 2*a1*a3 - 2*a3*a4
    res[4] = R::dot_product(&[two_a0, two_a1], &[a[4], a[3]]) + a[2].square() - two_a3_a4;
}

#[inline]
fn quintic_inv<F: QuinticExtendable>(a: &QuinticExtensionField<F>) -> QuinticExtensionField<F> {
    // Writing 'a' for self, we need to compute: `prod_conj = a^{q^4 + q^3 + q^2 + q}`
    let a_exp_q = a.frobenius();
    let a_exp_q_plus_q_sq = (*a * a_exp_q).frobenius();
    let prod_conj = a_exp_q_plus_q_sq * a_exp_q_plus_q_sq.repeated_frobenius(2);

    // norm = a * prod_conj is in the base field, so only compute that
    // coefficient rather than the full product.
    let norm = F::dot_product::<5>(
        &a.value,
        &[
            prod_conj.value[0],
            prod_conj.value[4],
            prod_conj.value[3],
            prod_conj.value[2],
            prod_conj.value[1] - prod_conj.value[4],
        ],
    );

    debug_assert_eq!(QuinticExtensionField::<F>::from(norm), *a * prod_conj);

    prod_conj * norm.inverse()
}

// fn compute_frobenius_matrix<F: QuinticExtendable>() {
//     for i in 1..5 {
//         let mut x = QuinticExtensionField::<F>::default();
//         x.value[i] = F::ONE;
//         let x = x.exp_u64(F::order().to_u64_digits()[0]);
//         print!("\n[");
//         for j in 0..5 {
//             print!(" MontyField31::new({}), ", x.value[j]);
//         }
//         print!("], ");
//     }
//     std::io::Write::flush(&mut std::io::stdout()).unwrap();
// }
