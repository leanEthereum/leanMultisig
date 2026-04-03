// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use crate::{MontyParameters, base_mul_packed, monty_add, monty_sub};
use field::{Algebra, Field, PrimeCharacteristicRing, packed_mod_add, packed_mod_sub};

use crate::packed_extension::PackedQuinticExtensionField;
use crate::packing::quintic_mul_packed;
use crate::quintic_extension::extension::QuinticExtensionField;
use crate::{KoalaBear, KoalaBearParameters};

pub mod extension;
pub(crate) mod packed_extension;
pub(crate) mod packing;

pub type QuinticExtensionFieldKB = QuinticExtensionField<KoalaBear>;
pub type PackedQuinticExtensionFieldKB = PackedQuinticExtensionField<KoalaBear, <KoalaBear as Field>::Packing>;

impl QuinticExtendable for KoalaBear {
    /// Frobenius matrix for X^5 + 2 over F_p where p = 4194304001.
    /// Since X^5 + 2 is a binomial extension and p ≡ 1 (mod 5), the Frobenius is diagonal:
    /// X^{ip} = w^i * X^i where w = (-2)^((p-1)/5).
    const FROBENIUS_MATRIX: [[Self; 5]; 4] = [
        [
            Self::new(0),
            Self::new(561393150),
            Self::new(0),
            Self::new(0),
            Self::new(0),
        ],
        [
            Self::new(0),
            Self::new(0),
            Self::new(1307621960),
            Self::new(0),
            Self::new(0),
        ],
        [
            Self::new(0),
            Self::new(0),
            Self::new(0),
            Self::new(1448665303),
            Self::new(0),
        ],
        [
            Self::new(0),
            Self::new(0),
            Self::new(0),
            Self::new(0),
            Self::new(876623587),
        ],
    ];

    const EXT_GENERATOR: [Self; 5] = Self::new_array([2, 1, 0, 0, 0]);
}

impl QuinticExtendableAlgebra<KoalaBear> for KoalaBear {
    #[inline(always)]
    fn quintic_mul(a: &[Self; 5], b: &[Self; 5], res: &mut [Self; 5]) {
        quintic_mul_packed(a, b, res);
    }

    #[inline(always)]
    fn quintic_add(a: &[Self; 5], b: &[Self; 5]) -> [Self; 5] {
        let mut res = [Self::ZERO; 5];
        unsafe {
            // Safe as Self is repr(transparent) and stores a single u32.
            let a: &[u32; 5] = &*(a.as_ptr() as *const [u32; 5]);
            let b: &[u32; 5] = &*(b.as_ptr() as *const [u32; 5]);
            let res: &mut [u32; 5] = &mut *(res.as_mut_ptr() as *mut [u32; 5]);

            packed_mod_add(a, b, res, KoalaBearParameters::PRIME, monty_add::<KoalaBearParameters>);
        }
        res
    }

    #[inline(always)]
    fn quintic_sub(a: &[Self; 5], b: &[Self; 5]) -> [Self; 5] {
        let mut res = [Self::ZERO; 5];
        unsafe {
            // Safe as Self is repr(transparent) and stores a single u32.
            let a: &[u32; 5] = &*(a.as_ptr() as *const [u32; 5]);
            let b: &[u32; 5] = &*(b.as_ptr() as *const [u32; 5]);
            let res: &mut [u32; 5] = &mut *(res.as_mut_ptr() as *mut [u32; 5]);

            packed_mod_sub(a, b, res, KoalaBearParameters::PRIME, monty_sub::<KoalaBearParameters>);
        }
        res
    }

    #[inline(always)]
    fn quintic_base_mul(lhs: [Self; 5], rhs: Self) -> [Self; 5] {
        let mut res = [Self::ZERO; 5];
        base_mul_packed(lhs, rhs, &mut res);
        res
    }
}

/// Trait for fields that support quintic extension of the form: `F[X]/(X^5 + 2)`
pub trait QuinticExtendable: Field + QuinticExtendableAlgebra<Self> {
    const FROBENIUS_MATRIX: [[Self; 5]; 4];

    /// A generator for the extension field, expressed as a degree-`D` polynomial.
    ///
    /// This is an array of size `D`, where each entry is a base field element.
    const EXT_GENERATOR: [Self; 5];
}

pub trait QuinticExtendableAlgebra<F: Field>: Algebra<F> {
    /// Multiplication in the algebra extension ring `A<X> / (X^D - W)`.
    ///
    /// Some algebras may want to reimplement this with faster methods.
    fn quintic_mul(a: &[Self; 5], b: &[Self; 5], res: &mut [Self; 5]);

    /// Addition of elements in the algebra extension ring `A<X> / (X^D - W)`.
    ///
    /// As addition has no dependence on `W` so this is equivalent
    /// to an algorithm for adding arrays of elements of `A`.
    ///
    /// Some algebras may want to reimplement this with faster methods.
    #[must_use]
    fn quintic_add(a: &[Self; 5], b: &[Self; 5]) -> [Self; 5];

    /// Subtraction of elements in the algebra extension ring `A<X> / (X^D - W)`.
    ///
    /// As subtraction has no dependence on `W` so this is equivalent
    /// to an algorithm for subtracting arrays of elements of `A`.
    ///
    /// Some algebras may want to reimplement this with faster methods.
    #[must_use]
    fn quintic_sub(a: &[Self; 5], b: &[Self; 5]) -> [Self; 5];

    fn quintic_base_mul(lhs: [Self; 5], rhs: Self) -> [Self; 5];
}
