#![cfg_attr(not(test), warn(unused_crate_dependencies))]

use core::ops::{Add, Mul, Sub};
use field::PrimeCharacteristicRing;

mod symbolic;
pub use symbolic::*;

mod constraint_folder;
pub use constraint_folder::*;

pub trait Air: Send + Sync + 'static {
    type ExtraData: Send + Sync + 'static;

    fn degree_air(&self) -> usize;

    fn n_columns(&self) -> usize;

    fn n_constraints(&self) -> usize;

    fn down_column_indexes(&self) -> Vec<usize>;

    fn eval<AB: AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData);

    fn n_down_columns(&self) -> usize {
        self.down_column_indexes().len()
    }
}

pub trait AirBuilder: Sized {
    type F: PrimeCharacteristicRing + 'static;
    type EF: PrimeCharacteristicRing
        + 'static
        + Add<Self::F, Output = Self::EF>
        + Mul<Self::F, Output = Self::EF>
        + Sub<Self::F, Output = Self::EF>
        + From<Self::F>;

    fn up(&self) -> &[Self::F];
    fn down(&self) -> &[Self::F];

    fn assert_zero(&mut self, x: Self::F);
    fn assert_zero_ef(&mut self, x: Self::EF);

    fn eval_virtual_column(&mut self, x: Self::EF);

    fn assert_eq(&mut self, x: Self::F, y: Self::F) {
        self.assert_zero(x - y);
    }

    fn assert_bool(&mut self, x: Self::F) {
        self.assert_zero(x.bool_check());
    }

    /// useful to build the recursion program
    #[inline(always)]
    fn declare_values(&mut self, values: &[Self::F]) {
        let _ = values;
    }
}
