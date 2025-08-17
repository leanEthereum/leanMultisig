use crate::{constant::F, memory::address::MemoryAddress};

/// Holds the high-level witness data for a single Poseidon2 permutation over 16 elements.
#[derive(Debug)]
pub struct WitnessPoseidon16 {
    /// The CPU cycle at which this operation is initiated, if applicable.
    pub cycle: Option<usize>,
    /// The memory address (vectorized pointer, of size 1) of the first 8-element input vector.
    pub addr_input_a: MemoryAddress,
    /// The memory address (vectorized pointer, of size 1) of the second 8-element input vector.
    pub addr_input_b: MemoryAddress,
    /// The memory address (vectorized pointer, of size 2) where the two 8-element output vectors are stored.
    pub addr_output: MemoryAddress,
    /// The full 16-element input state for the permutation.
    pub input: [F; 16],
    /// The full 16-element output state resulting from the permutation.
    pub output: [F; 16],
}

/// Holds the high-level witness data for a single Poseidon2 permutation over 24 elements.
#[derive(Debug)]
pub struct WitnessPoseidon24 {
    /// The CPU cycle at which this operation is initiated, if applicable.
    pub cycle: Option<usize>,
    /// The memory address (vectorized pointer, of size 2) of the first two 8-element input vectors.
    pub addr_input_a: usize,
    /// The memory address (vectorized pointer, of size 1) of the third 8-element input vector.
    pub addr_input_b: usize,
    /// The memory address (vectorized pointer, of size 1) where the relevant 8-element output vector is stored.
    pub addr_output: usize,
    /// The full 24-element input state for the permutation.
    pub input: [F; 24],
    /// The last 8 elements of the 24-element output state from the permutation.
    pub output: [F; 8],
}
