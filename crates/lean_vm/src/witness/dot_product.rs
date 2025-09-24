//! Dot product witness for arithmetic operations between extension field elements

use crate::core::{EF, F};
use p3_field::PrimeCharacteristicRing;

/// Witness data for dot the product precompile
#[derive(Debug, Clone)]
pub struct WitnessDotProduct {
    /// Execution cycle when this operation occurred
    pub cycle: usize,
    /// Memory address of first input vector (normal pointer)
    pub addr_0: usize,
    /// Memory address of second input vector (normal pointer)
    pub addr_1: usize,
    /// Memory address where result is stored (normal pointer)
    pub addr_res: usize,
    /// Length of the input vectors
    pub len: usize,
    /// First input vector data
    pub slice_0: Vec<EF>,
    /// Second input vector data
    pub slice_1: Vec<EF>,
    /// Computed dot product result
    pub res: EF,
}

impl WitnessDotProduct {
    /// Get memory addresses and vector length as field elements
    pub fn addresses_and_len_field_repr(&self) -> [F; 4] {
        [
            F::from_usize(self.addr_0),
            F::from_usize(self.addr_1),
            F::from_usize(self.addr_res),
            F::from_usize(self.len),
        ]
    }
}
