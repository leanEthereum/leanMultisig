//! Poseidon2 hash witness for 16-element input

use crate::core::{F, POSEIDON_16_NULL_HASH_PTR, ZERO_VEC_PTR};
use p3_field::PrimeCharacteristicRing;
use p3_symmetric::Permutation;
use utils::get_poseidon16;

/// Witness data for Poseidon2 cryptographic hash operations with 16-element input
///
/// This witness captures all the information needed to verify a Poseidon2 hash computation
/// including input data, output hash, and memory addresses involved.
#[derive(Debug, Clone)]
pub struct WitnessPoseidon16 {
    /// Execution cycle when this hash occurred (None for precomputed values)
    pub cycle: Option<usize>,
    /// Memory address of first input vector (vectorized pointer, size 1)
    pub addr_input_a: usize,
    /// Memory address of second input vector (vectorized pointer, size 1)
    pub addr_input_b: usize,
    /// Memory address where hash output is stored (vectorized pointer, size 2)
    pub addr_output: usize,
    /// Complete 16-element input to the hash function
    pub input: [F; 16],
    /// Complete 16-element hash output
    pub output: [F; 16],
}

impl WitnessPoseidon16 {
    /// Create a new Poseidon16 witness with all hash data
    pub const fn new(
        cycle: Option<usize>,
        addr_input_a: usize,
        addr_input_b: usize,
        addr_output: usize,
        input: [F; 16],
        output: [F; 16],
    ) -> Self {
        Self {
            cycle,
            addr_input_a,
            addr_input_b,
            addr_output,
            input,
            output,
        }
    }

    /// Create a precomputed Poseidon16 witness for all-zero input
    ///
    /// This is used for common zero-input hashes that can be precomputed
    /// and stored at known memory locations for efficiency.
    pub fn poseidon_of_zero() -> Self {
        Self {
            cycle: None,
            addr_input_a: ZERO_VEC_PTR,
            addr_input_b: ZERO_VEC_PTR,
            addr_output: POSEIDON_16_NULL_HASH_PTR,
            input: [F::ZERO; 16],
            output: get_poseidon16().permute([F::ZERO; 16]),
        }
    }

    /// Get all memory addresses as field element representation
    ///
    /// Returns [addr_input_a, addr_input_b, addr_output] as base field elements
    pub fn addresses_field_repr(&self) -> [F; 3] {
        [
            F::from_usize(self.addr_input_a),
            F::from_usize(self.addr_input_b),
            F::from_usize(self.addr_output),
        ]
    }
}
