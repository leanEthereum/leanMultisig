// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

//! A couple of simple functions needed in the case that this is compiled without architecture optimizations available.

mod poseidon2;

pub use poseidon2::*;

use crate::{FieldParameters, MontyField31};

/// Multiplication by a base field element in a binomial extension field.
#[inline]
pub fn base_mul_packed<FP, const WIDTH: usize>(
    a: [MontyField31<FP>; WIDTH],
    b: MontyField31<FP>,
    res: &mut [MontyField31<FP>; WIDTH],
) where
    FP: FieldParameters,
{
    res.iter_mut().zip(a.iter()).for_each(|(r, a)| *r = *a * b);
}
