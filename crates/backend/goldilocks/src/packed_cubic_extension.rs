// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

//! Packed (SIMD) version of the cubic extension `F_p[X] / (X^3 - X - 1)`.
//!
//! Mirrors `koala-bear`'s `PackedQuinticExtensionField` shape: a SoA array of
//! `[PF; 3]` packed-base-field lanes, so each field operation is a SIMD
//! multiply/add over `PF::WIDTH` extension elements at once.

use alloc::vec::Vec;
use core::array;
use core::fmt::Debug;
use core::iter::{Product, Sum};
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use field::{
    Algebra, BasedVectorSpace, Field, PackedField, PackedFieldExtension, PackedValue, Powers, PrimeCharacteristicRing,
    field_to_array,
};
use itertools::Itertools;
use rand::distr::{Distribution, StandardUniform};
use serde::{Deserialize, Serialize};
use utils::{flatten_to_base, reconstitute_from_base};

use crate::Goldilocks;
use crate::cubic_extension::{CubicExtensionFieldGL, cubic_mul_generic, cubic_square_generic};

const D: usize = 3;

/// Packed cubic extension over `Goldilocks`, parameterized by base field packing `PF`.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Serialize, Deserialize, PartialOrd, Ord)]
#[repr(transparent)]
pub struct PackedCubicExtensionFieldGL<PF: PackedField<Scalar = Goldilocks>> {
    #[serde(
        with = "utils::array_serialization",
        bound(serialize = "PF: Serialize", deserialize = "PF: Deserialize<'de>")
    )]
    pub(crate) value: [PF; D],
}

impl<PF: PackedField<Scalar = Goldilocks>> PackedCubicExtensionFieldGL<PF> {
    const fn new(value: [PF; D]) -> Self {
        Self { value }
    }
}

impl<PF: PackedField<Scalar = Goldilocks>> Default for PackedCubicExtensionFieldGL<PF> {
    #[inline]
    fn default() -> Self {
        Self {
            value: array::from_fn(|_| PF::ZERO),
        }
    }
}

impl<PF: PackedField<Scalar = Goldilocks>> From<CubicExtensionFieldGL> for PackedCubicExtensionFieldGL<PF> {
    #[inline]
    fn from(x: CubicExtensionFieldGL) -> Self {
        Self {
            value: x.value.map(Into::into),
        }
    }
}

impl<PF: PackedField<Scalar = Goldilocks>> From<PF> for PackedCubicExtensionFieldGL<PF> {
    #[inline]
    fn from(x: PF) -> Self {
        Self {
            value: field_to_array(x),
        }
    }
}

impl<PF: PackedField<Scalar = Goldilocks>> Distribution<PackedCubicExtensionFieldGL<PF>> for StandardUniform
where
    Self: Distribution<PF>,
{
    #[inline]
    fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> PackedCubicExtensionFieldGL<PF> {
        PackedCubicExtensionFieldGL::new(array::from_fn(|_| self.sample(rng)))
    }
}

impl<PF: PackedField<Scalar = Goldilocks>> Algebra<CubicExtensionFieldGL> for PackedCubicExtensionFieldGL<PF> {}

impl<PF: PackedField<Scalar = Goldilocks>> Algebra<PF> for PackedCubicExtensionFieldGL<PF> {}

impl<PF: PackedField<Scalar = Goldilocks>> PrimeCharacteristicRing for PackedCubicExtensionFieldGL<PF> {
    type PrimeSubfield = PF::PrimeSubfield;

    const ZERO: Self = Self { value: [PF::ZERO; D] };

    const ONE: Self = Self {
        value: field_to_array(PF::ONE),
    };

    const TWO: Self = Self {
        value: field_to_array(PF::TWO),
    };

    const NEG_ONE: Self = Self {
        value: field_to_array(PF::NEG_ONE),
    };

    #[inline]
    fn from_prime_subfield(val: Self::PrimeSubfield) -> Self {
        PF::from_prime_subfield(val).into()
    }

    #[inline]
    fn from_bool(b: bool) -> Self {
        PF::from_bool(b).into()
    }

    #[inline(always)]
    fn square(&self) -> Self {
        let mut res = Self::default();
        cubic_square_generic(&self.value, &mut res.value);
        res
    }

    #[inline]
    fn zero_vec(len: usize) -> Vec<Self> {
        // SAFETY: this is a repr(transparent) wrapper around an array.
        unsafe { reconstitute_from_base(PF::zero_vec(len * D)) }
    }
}

impl<PF: PackedField<Scalar = Goldilocks>> BasedVectorSpace<PF> for PackedCubicExtensionFieldGL<PF> {
    const DIMENSION: usize = D;

    #[inline]
    fn as_basis_coefficients_slice(&self) -> &[PF] {
        &self.value
    }

    #[inline]
    fn from_basis_coefficients_fn<Fn: FnMut(usize) -> PF>(f: Fn) -> Self {
        Self {
            value: array::from_fn(f),
        }
    }

    #[inline]
    fn from_basis_coefficients_iter<I: ExactSizeIterator<Item = PF>>(mut iter: I) -> Option<Self> {
        (iter.len() == D).then(|| Self::new(array::from_fn(|_| iter.next().unwrap())))
    }

    #[inline]
    fn flatten_to_base(vec: Vec<Self>) -> Vec<PF> {
        // SAFETY: `Self` is `repr(transparent)` over `[PF; D]`.
        unsafe { flatten_to_base(vec) }
    }

    #[inline]
    fn reconstitute_from_base(vec: Vec<PF>) -> Vec<Self> {
        // SAFETY: `Self` is `repr(transparent)` over `[PF; D]`.
        unsafe { reconstitute_from_base(vec) }
    }
}

impl PackedFieldExtension<Goldilocks, CubicExtensionFieldGL>
    for PackedCubicExtensionFieldGL<<Goldilocks as Field>::Packing>
{
    #[inline]
    fn from_ext_slice(ext_slice: &[CubicExtensionFieldGL]) -> Self {
        let width = <Goldilocks as Field>::Packing::WIDTH;
        assert_eq!(ext_slice.len(), width);

        let res = array::from_fn(|i| <Goldilocks as Field>::Packing::from_fn(|j| ext_slice[j].value[i]));
        Self::new(res)
    }

    #[inline]
    fn to_ext_iter(iter: impl IntoIterator<Item = Self>) -> impl Iterator<Item = CubicExtensionFieldGL> {
        let width = <Goldilocks as Field>::Packing::WIDTH;
        iter.into_iter().flat_map(move |x| {
            (0..width).map(move |i| {
                let values = array::from_fn(|j| x.value[j].as_slice()[i]);
                CubicExtensionFieldGL::new(values)
            })
        })
    }

    #[inline]
    fn packed_ext_powers(base: CubicExtensionFieldGL) -> Powers<Self> {
        let width = <Goldilocks as Field>::Packing::WIDTH;
        let powers = base.powers().take(width + 1).collect_vec();
        let current = Self::from_ext_slice(&powers[..width]);
        let multiplier = powers[width].into();

        Powers {
            base: multiplier,
            current,
        }
    }
}

impl<PF: PackedField<Scalar = Goldilocks>> Neg for PackedCubicExtensionFieldGL<PF> {
    type Output = Self;
    #[inline]
    fn neg(self) -> Self {
        Self {
            value: self.value.map(PF::neg),
        }
    }
}

impl<PF: PackedField<Scalar = Goldilocks>> Add for PackedCubicExtensionFieldGL<PF> {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        Self {
            value: array::from_fn(|i| self.value[i] + rhs.value[i]),
        }
    }
}

impl<PF: PackedField<Scalar = Goldilocks>> Add<CubicExtensionFieldGL> for PackedCubicExtensionFieldGL<PF> {
    type Output = Self;
    #[inline]
    fn add(self, rhs: CubicExtensionFieldGL) -> Self {
        Self {
            value: array::from_fn(|i| self.value[i] + rhs.value[i]),
        }
    }
}

impl<PF: PackedField<Scalar = Goldilocks>> Add<PF> for PackedCubicExtensionFieldGL<PF> {
    type Output = Self;
    #[inline]
    fn add(mut self, rhs: PF) -> Self {
        self.value[0] += rhs;
        self
    }
}

impl<PF: PackedField<Scalar = Goldilocks>> AddAssign for PackedCubicExtensionFieldGL<PF> {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        for i in 0..D {
            self.value[i] += rhs.value[i];
        }
    }
}

impl<PF: PackedField<Scalar = Goldilocks>> AddAssign<CubicExtensionFieldGL> for PackedCubicExtensionFieldGL<PF> {
    #[inline]
    fn add_assign(&mut self, rhs: CubicExtensionFieldGL) {
        for i in 0..D {
            self.value[i] += rhs.value[i];
        }
    }
}

impl<PF: PackedField<Scalar = Goldilocks>> AddAssign<PF> for PackedCubicExtensionFieldGL<PF> {
    #[inline]
    fn add_assign(&mut self, rhs: PF) {
        self.value[0] += rhs;
    }
}

impl<PF: PackedField<Scalar = Goldilocks>> Sum for PackedCubicExtensionFieldGL<PF> {
    #[inline]
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|acc, x| acc + x).unwrap_or(Self::ZERO)
    }
}

impl<PF: PackedField<Scalar = Goldilocks>> Sub for PackedCubicExtensionFieldGL<PF> {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Self) -> Self {
        Self {
            value: array::from_fn(|i| self.value[i] - rhs.value[i]),
        }
    }
}

impl<PF: PackedField<Scalar = Goldilocks>> Sub<CubicExtensionFieldGL> for PackedCubicExtensionFieldGL<PF> {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: CubicExtensionFieldGL) -> Self {
        Self {
            value: array::from_fn(|i| self.value[i] - rhs.value[i]),
        }
    }
}

impl<PF: PackedField<Scalar = Goldilocks>> Sub<PF> for PackedCubicExtensionFieldGL<PF> {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: PF) -> Self {
        let mut res = self.value;
        res[0] -= rhs;
        Self { value: res }
    }
}

impl<PF: PackedField<Scalar = Goldilocks>> SubAssign for PackedCubicExtensionFieldGL<PF> {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl<PF: PackedField<Scalar = Goldilocks>> SubAssign<CubicExtensionFieldGL> for PackedCubicExtensionFieldGL<PF> {
    #[inline]
    fn sub_assign(&mut self, rhs: CubicExtensionFieldGL) {
        *self = *self - rhs;
    }
}

impl<PF: PackedField<Scalar = Goldilocks>> SubAssign<PF> for PackedCubicExtensionFieldGL<PF> {
    #[inline]
    fn sub_assign(&mut self, rhs: PF) {
        *self = *self - rhs;
    }
}

impl<PF: PackedField<Scalar = Goldilocks>> Mul for PackedCubicExtensionFieldGL<PF> {
    type Output = Self;
    #[inline(always)]
    fn mul(self, rhs: Self) -> Self {
        let mut res = Self::default();
        cubic_mul_generic(&self.value, &rhs.value, &mut res.value);
        res
    }
}

impl<PF: PackedField<Scalar = Goldilocks>> Mul<CubicExtensionFieldGL> for PackedCubicExtensionFieldGL<PF> {
    type Output = Self;
    #[inline(always)]
    fn mul(self, rhs: CubicExtensionFieldGL) -> Self {
        let b: [PF; D] = rhs.value.map(|x| x.into());
        let mut res = Self::default();
        cubic_mul_generic(&self.value, &b, &mut res.value);
        res
    }
}

impl<PF: PackedField<Scalar = Goldilocks>> Mul<PF> for PackedCubicExtensionFieldGL<PF> {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: PF) -> Self {
        Self {
            value: self.value.map(|x| x * rhs),
        }
    }
}

impl<PF: PackedField<Scalar = Goldilocks>> Product for PackedCubicExtensionFieldGL<PF> {
    #[inline]
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|acc, x| acc * x).unwrap_or(Self::ONE)
    }
}

impl<PF: PackedField<Scalar = Goldilocks>> MulAssign for PackedCubicExtensionFieldGL<PF> {
    #[inline(always)]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl<PF: PackedField<Scalar = Goldilocks>> MulAssign<CubicExtensionFieldGL> for PackedCubicExtensionFieldGL<PF> {
    #[inline(always)]
    fn mul_assign(&mut self, rhs: CubicExtensionFieldGL) {
        *self = *self * rhs;
    }
}

impl<PF: PackedField<Scalar = Goldilocks>> MulAssign<PF> for PackedCubicExtensionFieldGL<PF> {
    #[inline]
    fn mul_assign(&mut self, rhs: PF) {
        *self = *self * rhs;
    }
}
