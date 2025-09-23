//! Multilinear polynomial evaluation witness

use crate::core::{EF, F};
use p3_field::PrimeCharacteristicRing;

/// Row data for multilinear polynomial evaluation
///
/// Contains the core data needed for a multilinear evaluation operation
/// including memory addresses, evaluation point, and result.
#[derive(Debug, Clone)]
pub struct RowMultilinearEval {
    /// Memory address of polynomial coefficients
    pub addr_coeffs: usize,
    /// Memory address of evaluation point
    pub addr_point: usize,
    /// Memory address where result is stored
    pub addr_res: usize,
    /// Evaluation point coordinates (one per variable)
    pub point: Vec<EF>,
    /// Computed evaluation result
    pub res: EF,
}

impl RowMultilinearEval {
    /// Create a new multilinear evaluation row with all required data
    pub fn new(
        addr_coeffs: usize,
        addr_point: usize,
        addr_res: usize,
        point: Vec<EF>,
        res: EF,
    ) -> Self {
        Self {
            addr_coeffs,
            addr_point,
            addr_res,
            point,
            res,
        }
    }

    /// Get the number of variables in this multilinear polynomial
    ///
    /// This is determined by the length of the evaluation point vector
    pub const fn n_vars(&self) -> usize {
        self.point.len()
    }

    /// Get memory addresses and variable count as field element representation
    ///
    /// Returns [addr_coeffs, addr_point, addr_res, n_vars] as base field elements
    pub fn addresses_and_n_vars_field_repr(&self) -> [F; 4] {
        [
            F::from_usize(self.addr_coeffs),
            F::from_usize(self.addr_point),
            F::from_usize(self.addr_res),
            F::from_usize(self.n_vars()),
        ]
    }
}

/// Complete witness for multilinear polynomial evaluation with execution context
///
/// Combines the row data with cycle information to provide full execution trace details
#[derive(Debug, Clone, derive_more::Deref)]
pub struct WitnessMultilinearEval {
    /// Execution cycle when this evaluation occurred
    pub cycle: usize,
    /// Core multilinear evaluation data
    #[deref]
    pub inner: RowMultilinearEval,
}

impl WitnessMultilinearEval {
    /// Create a new multilinear evaluation witness
    pub const fn new(cycle: usize, inner: RowMultilinearEval) -> Self {
        Self { cycle, inner }
    }
}
