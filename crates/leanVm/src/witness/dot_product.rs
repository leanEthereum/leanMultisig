use crate::{constant::EF, memory::address::MemoryAddress};

/// Holds the high-level witness data for a single dot product precompile execution.
#[derive(Debug)]
pub struct WitnessDotProduct {
    /// The CPU cycle at which the dot product operation is initiated.
    pub cycle: usize,
    /// The starting memory address (vectorized pointer) of the first input slice.
    pub addr_0: MemoryAddress,
    /// The starting memory address (vectorized pointer) of the second input slice.
    pub addr_1: MemoryAddress,
    /// The memory address (vectorized pointer) where the final result is stored.
    pub addr_res: MemoryAddress,
    /// The number of elements in each input slice.
    pub len: usize,
    /// The actual data values of the first input slice.
    pub slice_0: Vec<EF>,
    /// The actual data values of the second input slice.
    pub slice_1: Vec<EF>,
    /// The final computed result of the dot product.
    pub res: EF,
}
