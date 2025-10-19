//! Poseidon2 hash witness for 16-element input

use crate::core::{F, POSEIDON_16_NULL_HASH_PTR, ZERO_VEC_PTR};
use p3_field::PrimeCharacteristicRing;

/// Witness data for Poseidon2 over 16 field elements
#[derive(Debug, Clone)]
pub struct WitnessPoseidon16 {
    /// Execution cycle when this hash occurred (None when padding)
    pub cycle: Option<usize>,
    /// Memory address of first input vector (vectorized pointer, size 1)
    pub addr_input_a: usize,
    /// Memory address of second input vector (vectorized pointer, size 1)
    pub addr_input_b: usize,
    /// Memory address where hash output is stored (vectorized pointer, size 2)
    pub addr_output: usize,
    /// Complete 16-element input to the hash function
    pub input: [F; 16],
    /// Whether this was a compression (2-to-1) or not (2-to-2)
    pub is_compression: bool,
}

impl WitnessPoseidon16 {
    /// Create a precomputed Poseidon16 witness for all-zero input
    ///
    /// This is useful for padding.
    pub fn poseidon_of_zero() -> Self {
        Self {
            cycle: None,
            addr_input_a: ZERO_VEC_PTR,
            addr_input_b: ZERO_VEC_PTR,
            addr_output: POSEIDON_16_NULL_HASH_PTR,
            input: [F::ZERO; 16],
            is_compression: true,
        }
    }

    /// Get all memory addresses as field elements
    pub fn addresses_field_repr(&self) -> [F; 4] {
        [
            F::from_usize(self.addr_input_a),
            F::from_usize(self.addr_input_b),
            F::from_usize(self.addr_output),
            F::from_bool(self.is_compression),
        ]
    }
}
