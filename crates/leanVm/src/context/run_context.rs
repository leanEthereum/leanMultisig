use crate::{
    bytecode::operand::{MemOrConstant, MemOrFp, MemOrFpOrConstant},
    errors::{memory::MemoryError, vm::VirtualMachineError},
    memory::{address::MemoryAddress, manager::MemoryManager, val::MemoryValue},
};

#[derive(Debug, Default)]
pub struct RunContext {
    /// The address in memory of the current instruction to be executed.
    pub(crate) pc: MemoryAddress,
    /// Points to the beginning of the stack frame of the current function.
    ///
    /// The value of `fp` stays the same fopr all the instructions in the same invocation of a function.
    pub(crate) fp: MemoryAddress,

    /// Runtime allocation pointer (scalar).
    ///
    /// This register is **not part of the verifier-visible state**, and is not encoded in the trace.
    /// It is used internally by the prover to keep track of memory allocations for scalar data
    /// during execution (e.g., frame-local temporary values).
    ///
    /// Memory is allocated from `ap` using hints inserted at compile time, usually before a function call.
    /// Its value increases over time and does not decrease, following a stack-like discipline.
    ///
    /// While `ap` determines where memory is written at runtime, its usage is opaque to the verifier.
    /// Instead, memory layout is statically determined and reflected through hint instructions that
    /// record where allocations were made.
    pub(crate) ap: MemoryAddress,

    /// Runtime allocation pointer (vectorized, chunked by `DIMENSION` field elements).
    ///
    /// Similar to [`ap`], but used for allocating vectors of field elements — typically inputs or outputs
    /// of Poseidon2 and extension field operations.
    ///
    /// The prover uses `ap_vectorized` to ensure proper alignment and avoid memory collisions for
    /// multi-element data structures. Each allocation consumes a full vector chunk, and the pointer
    /// advances accordingly.
    ///
    /// Like `ap`, this value is **not exposed to the verifier**. Its sole role is to guide prover-side
    /// allocation logic during execution.
    pub(crate) ap_vectorized: MemoryAddress,
}

impl RunContext {
    #[must_use]
    pub const fn new(
        pc: MemoryAddress,
        fp: MemoryAddress,
        ap: MemoryAddress,
        ap_vectorized: MemoryAddress,
    ) -> Self {
        Self {
            pc,
            fp,
            ap,
            ap_vectorized,
        }
    }

    #[must_use]
    pub const fn pc(&self) -> &MemoryAddress {
        &self.pc
    }

    #[must_use]
    pub const fn fp(&self) -> &MemoryAddress {
        &self.fp
    }

    /// Resolves a `MemOrConstant` operand to its final value.
    ///
    /// - If the operand is a constant, it returns the constant.
    /// - If it's a memory location, it computes the address relative to `fp` and fetches the value from memory.
    pub fn value_from_mem_or_constant(
        &self,
        operand: &MemOrConstant,
        memory: &MemoryManager,
    ) -> Result<MemoryValue, MemoryError> {
        match operand {
            MemOrConstant::Constant(val) => Ok(MemoryValue::Int(*val)),
            MemOrConstant::MemoryAfterFp { shift } => {
                let addr = (self.fp + *shift)?;
                memory
                    .get(addr)
                    .ok_or(MemoryError::UninitializedMemory(addr))
            }
        }
    }

    /// Resolves a `MemOrFp` operand to its final value.
    ///
    /// - If the operand is the frame pointer `Fp`, it returns the `fp` address itself.
    /// - If it's a memory location, it computes the address relative to `fp` and fetches the value.
    pub fn value_from_mem_or_fp(
        &self,
        operand: &MemOrFp,
        memory: &MemoryManager,
    ) -> Result<MemoryValue, MemoryError> {
        match operand {
            MemOrFp::Fp => Ok(MemoryValue::Address(self.fp)),
            MemOrFp::MemoryAfterFp { shift } => {
                let addr = (self.fp + *shift)?;
                memory
                    .get(addr)
                    .ok_or(MemoryError::UninitializedMemory(addr))
            }
        }
    }

    /// Resolves a `MemOrFpOrConstant` operand to its final value.
    ///
    /// This is a comprehensive resolver that handles all three potential operand types:
    /// - a constant value,
    /// - a memory location relative to `fp`,
    /// - the `fp` register itself.
    pub fn value_from_mem_or_fp_or_constant(
        &self,
        operand: &MemOrFpOrConstant,
        memory: &MemoryManager,
    ) -> Result<MemoryValue, VirtualMachineError> {
        match operand {
            MemOrFpOrConstant::Constant(val) => Ok(MemoryValue::Int(*val)),
            MemOrFpOrConstant::Fp => Ok(MemoryValue::Address(self.fp)),
            MemOrFpOrConstant::MemoryAfterFp { shift } => {
                let addr = (self.fp + *shift)?;
                memory
                    .get(addr)
                    .ok_or_else(|| MemoryError::UninitializedMemory(addr).into())
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use p3_field::PrimeCharacteristicRing;

    use super::*;
    use crate::constant::F;

    #[test]
    fn test_get_value_constant() {
        // Create a dummy RunContext with pc and fp.
        let ctx = RunContext::new(
            MemoryAddress {
                segment_index: 0,
                offset: 0,
            },
            MemoryAddress {
                segment_index: 1,
                offset: 0,
            },
            MemoryAddress::default(),
            MemoryAddress::default(),
        );

        // A constant operand with field element 42.
        let operand = MemOrConstant::Constant(F::from_u64(42));

        // Run `value_from_mem_or_constant` with an unused memory manager (memory is not needed for constants).
        let memory = MemoryManager::default();

        // It should return the wrapped constant as a MemoryValue::Int.
        let result = ctx.value_from_mem_or_constant(&operand, &memory).unwrap();
        assert_eq!(result, MemoryValue::Int(F::from_u64(42)));
    }

    #[test]
    fn test_get_value_memory_after_fp_success() {
        let mut memory = MemoryManager::default();

        // Add a segment that will be used for `fp`.
        let fp = memory.add(); // segment_index = 0, offset = 0

        // Shift = 2, so address to read is fp + 2 => offset 2 in the same segment.
        let addr_to_read = MemoryAddress {
            segment_index: fp.segment_index,
            offset: fp.offset + 2,
        };

        // Insert a value at that address manually.
        let expected_val = MemoryValue::Int(F::from_u64(99));
        memory.memory.insert(addr_to_read, expected_val).unwrap();

        // Create a RunContext with that fp.
        let ctx = RunContext::new(
            MemoryAddress {
                segment_index: 0,
                offset: 0,
            }, // dummy pc
            fp,
            MemoryAddress::default(),
            MemoryAddress::default(),
        );

        // The operand asks to read memory at fp + 2.
        let operand = MemOrConstant::MemoryAfterFp { shift: 2 };

        // Call value_from_mem_or_constant, which should fetch the value we inserted.
        let result = ctx.value_from_mem_or_constant(&operand, &memory).unwrap();
        assert_eq!(result, expected_val);
    }

    #[test]
    fn test_get_value_memory_after_fp_uninitialized_memory() {
        let mut memory = MemoryManager::default();

        // Create a segment and set fp to its base.
        let fp = memory.add(); // segment_index = 0, offset = 0

        // We won't insert anything, so all memory is uninitialized.

        // Shift = 1 → fp + 1 points to offset 1 (which is uninitialized).
        let operand: MemOrConstant = MemOrConstant::MemoryAfterFp { shift: 1 };

        // Set up context.
        let ctx = RunContext::new(
            MemoryAddress {
                segment_index: 0,
                offset: 0,
            }, // dummy pc
            fp,
            MemoryAddress::default(),
            MemoryAddress::default(),
        );

        // Calling value_from_mem_or_constant should return a VirtualMachineError::MemoryError::UninitializedMemory.
        let err = ctx
            .value_from_mem_or_constant(&operand, &memory)
            .unwrap_err();

        match err {
            MemoryError::UninitializedMemory(addr) => {
                assert_eq!(addr.segment_index, fp.segment_index);
                assert_eq!(addr.offset, fp.offset + 1);
            }
            other => panic!("Unexpected error: {other:?}"),
        }
    }

    #[test]
    fn test_get_value_from_mem_or_fp_or_constant_is_constant() {
        let ctx = RunContext::new(
            MemoryAddress::new(0, 0),
            MemoryAddress::new(1, 0),
            MemoryAddress::default(),
            MemoryAddress::default(),
        );
        let operand = MemOrFpOrConstant::Constant(F::from_u64(123));
        let memory = MemoryManager::default();
        let result = ctx
            .value_from_mem_or_fp_or_constant(&operand, &memory)
            .unwrap();
        assert_eq!(result, MemoryValue::Int(F::from_u64(123)));
    }

    #[test]
    fn test_get_value_from_mem_or_fp_or_constant_is_fp() {
        let fp_addr = MemoryAddress::new(1, 10);
        let ctx = RunContext::new(
            MemoryAddress::new(0, 0),
            fp_addr,
            MemoryAddress::default(),
            MemoryAddress::default(),
        );
        let operand = MemOrFpOrConstant::Fp;
        let memory = MemoryManager::default();
        let result = ctx
            .value_from_mem_or_fp_or_constant(&operand, &memory)
            .unwrap();
        assert_eq!(result, MemoryValue::Address(fp_addr));
    }

    #[test]
    fn test_get_value_from_mem_or_fp_or_constant_is_mem_success() {
        let mut memory = MemoryManager::default();
        let fp = memory.add();
        let addr_to_read = (fp + 7).unwrap();
        let expected_val = MemoryValue::Address(MemoryAddress::new(5, 5));
        memory.memory.insert(addr_to_read, expected_val).unwrap();

        let ctx = RunContext::new(
            MemoryAddress::new(0, 0),
            fp,
            MemoryAddress::default(),
            MemoryAddress::default(),
        );
        let operand = MemOrFpOrConstant::MemoryAfterFp { shift: 7 };
        let result = ctx
            .value_from_mem_or_fp_or_constant(&operand, &memory)
            .unwrap();
        assert_eq!(result, expected_val);
    }
}
