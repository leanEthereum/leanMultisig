// Credits: whir-p3 (https://github.com/tcoratger/whir-p3) (MIT and Apache-2.0 licenses).

mod commit;
pub use commit::*;
use poly::*;

mod open;
pub use open::*;

mod verify;
pub use verify::*;

mod dft;
pub use dft::*;

mod config;
pub use config::*;

mod merkle;
pub use merkle::DIGEST_ELEMS;
pub(crate) use merkle::*;

mod utils;
pub use utils::precompute_dft_twiddles;
pub(crate) use utils::*;

mod matrix;
pub(crate) use matrix::*;

#[derive(Clone, Debug)]
pub struct SparseStatement<EF> {
    pub total_num_variables: usize,
    pub point: MultilinearPoint<EF>,
    pub values: Vec<SparseValue<EF>>,
}

impl<EF> SparseStatement<EF> {
    pub fn new(total_num_variables: usize, point: MultilinearPoint<EF>, values: Vec<SparseValue<EF>>) -> Self {
        Self {
            total_num_variables,
            point,
            values,
        }
    }

    pub fn unique_value(total_num_variables: usize, index: usize, value: EF) -> Self {
        Self {
            total_num_variables,
            point: MultilinearPoint(vec![]),
            values: vec![SparseValue { selector: index, value }],
        }
    }

    pub fn dense(point: MultilinearPoint<EF>, value: EF) -> Self {
        Self {
            total_num_variables: point.len(),
            point,
            values: vec![SparseValue { selector: 0, value }],
        }
    }

    pub fn selector_num_variables(&self) -> usize {
        self.total_num_variables - self.inner_num_variables()
    }

    pub fn inner_num_variables(&self) -> usize {
        self.point.len()
    }
}

#[derive(Clone, Debug)]
pub struct SparseValue<EF> {
    pub selector: usize,
    pub value: EF,
}

impl<EF> SparseValue<EF> {
    pub fn new(selector: usize, value: EF) -> Self {
        Self { selector, value }
    }
}
