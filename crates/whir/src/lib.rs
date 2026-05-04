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

mod svo;
pub(crate) use svo::*;

#[derive(Clone, Debug)]
pub struct SparseStatement<EF> {
    pub total_num_variables: usize,
    pub point: MultilinearPoint<EF>,
    pub values: Vec<SparseValue<EF>>,
    /// When true, the weight polynomial is `next_mle(point, .)` instead of `eq(point, .)`.
    pub is_next: bool,
}

impl<EF> SparseStatement<EF> {
    pub fn new(total_num_variables: usize, point: MultilinearPoint<EF>, values: Vec<SparseValue<EF>>) -> Self {
        assert!(
            total_num_variables >= point.len(),
            "total_num_variables ({}) must be >= point.len() ({})",
            total_num_variables,
            point.len()
        );
        Self {
            total_num_variables,
            point,
            values,
            is_next: false,
        }
    }

    pub fn new_next(total_num_variables: usize, point: MultilinearPoint<EF>, values: Vec<SparseValue<EF>>) -> Self {
        assert!(
            total_num_variables >= point.len(),
            "total_num_variables ({}) must be >= point.len() ({})",
            total_num_variables,
            point.len()
        );
        Self {
            total_num_variables,
            point,
            values,
            is_next: true,
        }
    }

    pub fn unique_value(total_num_variables: usize, index: usize, value: EF) -> Self {
        Self {
            total_num_variables,
            point: MultilinearPoint(vec![]),
            values: vec![SparseValue { selector: index, value }],
            is_next: false,
        }
    }

    pub fn dense(point: MultilinearPoint<EF>, value: EF) -> Self {
        Self {
            total_num_variables: point.len(),
            point,
            values: vec![SparseValue { selector: 0, value }],
            is_next: false,
        }
    }

    pub fn selector_num_variables(&self) -> usize {
        self.total_num_variables
            .checked_sub(self.inner_num_variables())
            .expect("invariant violated: total_num_variables < point.len()")
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
