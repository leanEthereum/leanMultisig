//! Multilinear polynomial evaluation witness

use crate::core::{EF, F};
use p3_field::PrimeCharacteristicRing;

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
    pub const fn n_vars(&self) -> usize {
        self.point.len()
    }

    /// Get memory addresses and variable count as field elements
    pub fn addresses_and_n_vars_field_repr(&self) -> [F; 4] {
        [
            F::from_usize(self.addr_coeffs),
            F::from_usize(self.addr_point),
            F::from_usize(self.addr_res),
            F::from_usize(self.n_vars()),
        ]
    }
}

/// Witness for the multilinear_evaluation precompile
#[derive(Debug, Clone, derive_more::Deref)]
pub struct WitnessMultilinearEval {
    /// Execution cycle when this evaluation occurred
    pub cycle: usize,
    #[deref]
    pub inner: RowMultilinearEval,
}
