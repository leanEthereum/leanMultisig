// Credits: whir-p3 (https://github.com/tcoratger/whir-p3) (MIT and Apache-2.0 licenses).

mod commit;
pub use commit::*;
use field::ExtensionField;
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

/// Closure signature for [`RawWeights::PackedFill`]: called once with
/// `(combined_weights, gamma_pow)`, must perform
/// `combined_weights[i] += gamma_pow * weight_at_packing(i)` for every
/// packed entry it wants to contribute.
pub type PackedFillFn<EF> = Box<dyn FnOnce(&mut [EFPacking<EF>], EF) + Send>;

/// A pre-built dense weight polynomial together with its claimed
/// inner-product value against the committed polynomial. Used by
/// [`WhirConfig::prove_with_extras`] / [`WhirConfig::verify_with_extras`] to
/// fold custom weight polynomials (e.g. the jagged-PCS `F` polynomial)
/// directly into WHIR's initial sumcheck, instead of running a separate
/// dedicated sumcheck first.
///
/// Two forms are supported:
/// - [`RawWeights::Cube`] -- the caller materializes the cube evaluations
///   of length `2^num_variables` and `combine_statement` packs them into
///   the packed `combined_weights` buffer with the gamma power applied.
/// - [`RawWeights::PackedFill`] -- the caller supplies a closure that is
///   invoked once with the already-allocated packed `combined_weights`
///   buffer and the appropriate `gamma_pow`; the closure adds its
///   `gamma_pow`-scaled contribution directly. This lets a caller skip
///   materializing an intermediate `Vec<EF>` (and the subsequent
///   pack-and-add pass) when it can write the contribution in packed
///   form directly.
pub enum RawWeights<EF: ExtensionField<PF<EF>>> {
    Cube { cube_weights: Vec<EF>, claimed_sum: EF },
    PackedFill { fill: PackedFillFn<EF>, claimed_sum: EF },
}

impl<EF: ExtensionField<PF<EF>>> RawWeights<EF> {
    pub fn claimed_sum(&self) -> EF {
        match self {
            Self::Cube { claimed_sum, .. } | Self::PackedFill { claimed_sum, .. } => *claimed_sum,
        }
    }
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
