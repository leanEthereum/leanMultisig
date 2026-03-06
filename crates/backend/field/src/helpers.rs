// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use core::iter::Sum;
use core::mem::MaybeUninit;
use core::ops::Mul;

use crate::PrimeCharacteristicRing;

/// Extend a ring `R` element `x` to an array of length `D`
/// by filling zeros.
#[inline]
#[must_use]
pub const fn field_to_array<R: PrimeCharacteristicRing, const D: usize>(x: R) -> [R; D] {
    let mut arr = [const { MaybeUninit::uninit() }; D];
    arr[0] = MaybeUninit::new(x);
    let mut i = 1;
    while i < D {
        arr[i] = MaybeUninit::new(R::ZERO);
        i += 1;
    }
    unsafe { core::mem::transmute_copy::<_, [R; D]>(&arr) }
}

/// Given an element x from a 32 bit field F_P compute x/2.
#[inline]
#[must_use]
pub const fn halve_u32<const P: u32>(x: u32) -> u32 {
    let shift = (P + 1) >> 1;
    let half = x >> 1;
    if x & 1 == 0 { half } else { half + shift }
}

/// Maximally generic dot product.
#[must_use]
pub fn dot_product<S, LI, RI>(li: LI, ri: RI) -> S
where
    LI: Iterator,
    RI: Iterator,
    LI::Item: Mul<RI::Item>,
    S: Sum<<LI::Item as Mul<RI::Item>>::Output>,
{
    li.zip(ri).map(|(l, r)| l * r).sum()
}
