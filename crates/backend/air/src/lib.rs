#![cfg_attr(not(test), warn(unused_crate_dependencies))]

use core::ops::{Add, Mul, Sub};
use field::{Algebra, PrimeCharacteristicRing};

mod symbolic;
pub use symbolic::*;

mod constraint_folder;
pub use constraint_folder::*;

pub trait Air: Send + Sync + 'static {
    type ExtraData: Send + Sync + 'static;

    fn degree_air(&self) -> usize;

    fn n_columns(&self) -> usize;

    fn n_constraints(&self) -> usize;

    /// Number of "shift" columns (the ones that are also queried at the next
    /// row). By convention they occupy columns `0..n_shift_columns()` of the
    /// table; the remaining columns are "flat" (queried at the current row only).
    fn n_shift_columns(&self) -> usize;

    fn eval<AB: AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData);

    /// If the AIR contains a `low_degree_block` sub-region, returns `(degree, n_constraints)`
    fn low_degree_air(&self) -> Option<(usize, usize)> {
        None
    }
}

pub trait AirBuilder: Sized {
    /// Always the base field (or its SIMD packing).
    type F: PrimeCharacteristicRing + 'static;
    /// Intermediate field: equals F in base-field rounds, EF in extension rounds
    /// (or their respective SIMD packings).
    type IF: Algebra<Self::F> + 'static;
    /// Always the extension field (or its SIMD packing).
    type EF: PrimeCharacteristicRing
        + 'static
        + Add<Self::IF, Output = Self::EF>
        + Mul<Self::IF, Output = Self::EF>
        + Add<Self::F, Output = Self::EF>
        + Mul<Self::F, Output = Self::EF>
        + Sub<Self::F, Output = Self::EF>
        + From<Self::F>;

    /// Current-row column evaluations ("flat" view).
    fn flat(&self) -> &[Self::IF];
    /// Next-row column evaluations, restricted to the first `n_shift_columns()`
    /// columns (the "shift" view).
    fn shift(&self) -> &[Self::IF];

    fn assert_zero(&mut self, x: Self::IF);
    fn assert_zero_ef(&mut self, x: Self::EF);

    fn assert_eq(&mut self, x: Self::IF, y: Self::IF) {
        self.assert_zero(x - y);
    }

    fn assert_bool(&mut self, x: Self::IF) {
        self.assert_zero(x.bool_check());
    }

    fn assert_eq_low(&mut self, x: Self::IF, y: Self::IF) {
        self.assert_eq(x, y);
    }

    /// Execute `block` as a low-degree sub-region whose post-state is "cacheable"
    /// = linear in z without the low-degree constraints
    fn low_degree_block<F>(&mut self, state: &mut [Self::IF], block: F)
    where
        F: FnOnce(&mut Self, &mut [Self::IF]),
    {
        block(self, state);
    }

    /// useful to build the recursion program
    #[inline(always)]
    fn declare_values(&mut self, values: &[Self::IF]) {
        let _ = values;
    }
}
