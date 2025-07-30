use super::operand::MemOrConstant;

/// Hints are special instructions for the prover to resolve non-determinism.
///
/// They are not part of the verified computation trace.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Hint {
    /// A hint for the prover to allocate a new memory segment for a function's stack frame.
    ///
    /// This is the core mechanism for memory management in a VM without an `ap` (allocation pointer)
    /// register. The compiler pre-calculates the required memory size for each function.
    RequestMemory {
        /// The offset from `fp` where the pointer to the newly allocated segment will be stored.
        offset: usize,
        /// The requested size of the memory segment in scalar field elements.
        size: MemOrConstant,
        /// If true, the start of the allocated memory is aligned to an 8-element boundary
        /// to facilitate vectorized memory access for extension field operations.
        /// The value stored at `m[fp + offset]` will be the aligned address divided by 8.
        vectorized: bool,
    },
    /// A hint for the prover to compute the bit decomposition of a base field element.
    ///
    /// This is a non-deterministic operation used for operations like range checks
    /// or other logic required by the XMSS signature scheme.
    DecomposeBits {
        /// The starting offset from `fp` where the resulting bits will be stored.
        res_offset: usize,
        /// The field element that needs to be decomposed into its bits.
        to_decompose: MemOrConstant,
    },
    /// A hint used for debugging to print values from memory during execution.
    Print {
        /// A string containing line information (e.g., file and line number) for context.
        line_info: String,
        /// A list of memory locations or constants whose values should be printed.
        content: Vec<MemOrConstant>,
    },
}
