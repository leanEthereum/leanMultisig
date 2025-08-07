use p3_field::{Field, PrimeCharacteristicRing, PrimeField64};

use super::operand::MemOrConstant;
use crate::{
    constant::F, context::run_context::RunContext, errors::vm::VirtualMachineError,
    memory::manager::MemoryManager,
};

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

impl Hint {
    /// Executes a single hint emitted by the compiler during bytecode interpretation.
    ///
    /// Hints are runtime-only helper directives used for:
    /// - Allocating memory dynamically (`RequestMemory`)
    /// - Decomposing a field element into bits (`DecomposeBits`)
    /// - (Eventually) printing debug information (`Print`)
    ///
    /// These are not part of the trace or AIR and are only used by the prover for state setup or inspection.
    /// The verifier does not need to observe these effects.
    fn execute(
        &self,
        memory_manager: &mut MemoryManager,
        run_context: &mut RunContext,
    ) -> Result<(), VirtualMachineError> {
        match self {
            Self::RequestMemory {
                offset,
                size,
                vectorized,
            } => {
                // Resolve the `size` operand to a concrete field element.
                let size: F = run_context
                    .value_from_mem_or_constant(size, memory_manager)?
                    .try_into()?;
                // Convert the field element to a canonical `usize`.
                let size = size.as_canonical_u64() as usize;

                // Compute the address where the allocated pointer will be stored: `fp + offset`.
                let addr = (run_context.fp + *offset)?;

                if *vectorized {
                    // Store the current vectorized allocation pointer (`ap_vectorized`) at `addr`.
                    memory_manager
                        .memory
                        .insert(addr, run_context.ap_vectorized)?;

                    // Increase the vectorized allocation pointer by `size` (number of vectors).
                    run_context.ap_vectorized.offset += size;
                } else {
                    // Store the current scalar allocation pointer (`ap`) at `addr`.
                    memory_manager.memory.insert(addr, run_context.ap)?;

                    // Increase the scalar allocation pointer by `size` (number of scalars).
                    run_context.ap.offset += size;
                }
            }
            Self::DecomposeBits {
                res_offset,
                to_decompose,
            } => {
                // Resolve the operand to be decomposed into a concrete field element.
                let to_decompose: F = run_context
                    .value_from_mem_or_constant(to_decompose, memory_manager)?
                    .try_into()?;

                // Convert the field element to a native `u64` for bit-level manipulation.
                let to_decompose = to_decompose.as_canonical_u64();

                // For each bit position (up to the number of bits supported by the field):
                for i in 0..F::bits() {
                    // - Extract the i-th bit from the value using bit masking.
                    let bit = if to_decompose & (1 << i) != 0 {
                        F::ONE
                    } else {
                        F::ZERO
                    };

                    // - Compute the address at `fp + res_offset + i`.
                    // - Write the extracted bit to that memory location.
                    memory_manager
                        .memory
                        .insert(((run_context.fp + *res_offset)? + i)?, bit)?;
                }
            }
            Self::Print { .. } => {
                // TODO: implement
                // This is for debugging purposes only so this is not urgent for now.
            }
        }
        Ok(())
    }
}
