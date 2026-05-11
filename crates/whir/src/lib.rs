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

/// A pre-built dense weight polynomial together with its claimed
/// inner-product value against the committed polynomial. Used by
/// [`WhirConfig::prove_with_extras`] / [`WhirConfig::verify_with_extras`] to
/// fold custom weight polynomials (e.g. the jagged-PCS `F` polynomial)
/// directly into WHIR's initial sumcheck, instead of running a separate
/// dedicated sumcheck first.
///
/// On the prover side, `cube_weights` must contain the full cube
/// evaluations (length `2^num_variables`). The verifier-side counterpart is
/// the `extras_claimed_sums: Vec<EF>` argument to
/// [`WhirConfig::verify_with_extras`] plus a closure that computes the
/// weight polynomial's evaluation at WHIR's final folding point.
#[derive(Clone, Debug)]
pub struct RawWeights<EF> {
    pub cube_weights: Vec<EF>,
    pub claimed_sum: EF,
}

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
