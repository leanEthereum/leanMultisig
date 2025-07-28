use p3_field::PrimeField64;

use crate::{
    errors::{memory::MemoryError, vm::VirtualMachineError},
    memory::{address::MemoryAddress, manager::MemoryManager, val::MemoryValue},
    types::instruction::{MemOrConstant, MemOrFp, MemOrFpOrConstant},
};

#[derive(Debug, Default)]
pub struct RunContext {
    /// The address in memory of the current instruction to be executed.
    pub(crate) pc: MemoryAddress,
    /// Points to the beginning of the stack frame of the current function.
    ///
    /// The value of `fp` stays the same fopr all the instructions in the same invocation of a function.
    pub(crate) fp: MemoryAddress,
}

impl RunContext {
    #[must_use]
    pub const fn new(pc: MemoryAddress, fp: MemoryAddress) -> Self {
        Self { pc, fp }
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
    pub fn get_value<F>(
        &self,
        operand: &MemOrConstant<F>,
        memory: &MemoryManager,
    ) -> Result<MemoryValue<F>, VirtualMachineError<F>>
    where
        F: PrimeField64,
    {
        match operand {
            MemOrConstant::Constant(val) => Ok(MemoryValue::Int(*val)),
            MemOrConstant::MemoryAfterFp { shift } => {
                let addr = self.fp.add_usize(*shift)?;
                memory
                    .get(addr)
                    .ok_or_else(|| MemoryError::UninitializedMemory(addr).into())
            }
        }
    }

    /// Resolves a `MemOrFp` operand to its final value.
    ///
    /// - If the operand is the frame pointer `Fp`, it returns the `fp` address itself.
    /// - If it's a memory location, it computes the address relative to `fp` and fetches the value.
    pub fn get_value_from_mem_or_fp<F>(
        &self,
        operand: &MemOrFp,
        memory: &MemoryManager,
    ) -> Result<MemoryValue<F>, VirtualMachineError<F>>
    where
        F: PrimeField64,
    {
        match operand {
            MemOrFp::Fp => Ok(MemoryValue::Address(self.fp)),
            MemOrFp::MemoryAfterFp { shift } => {
                let addr = self.fp.add_usize(*shift)?;
                memory
                    .get(addr)
                    .ok_or_else(|| MemoryError::UninitializedMemory(addr).into())
            }
        }
    }

    /// Resolves a `MemOrFpOrConstant` operand to its final value.
    ///
    /// This is a comprehensive resolver that handles all three potential operand types:
    /// - a constant value,
    /// - a memory location relative to `fp`,
    /// - the `fp` register itself.
    pub fn get_value_from_mem_or_fp_or_constant<F>(
        &self,
        operand: &MemOrFpOrConstant<F>,
        memory: &MemoryManager,
    ) -> Result<MemoryValue<F>, VirtualMachineError<F>>
    where
        F: PrimeField64,
    {
        match operand {
            MemOrFpOrConstant::Constant(val) => Ok(MemoryValue::Int(*val)),
            MemOrFpOrConstant::Fp => Ok(MemoryValue::Address(self.fp)),
            MemOrFpOrConstant::MemoryAfterFp { shift } => {
                let addr = self.fp.add_usize(*shift)?;
                memory
                    .get(addr)
                    .ok_or_else(|| MemoryError::UninitializedMemory(addr).into())
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use p3_baby_bear::BabyBear;
    use p3_field::PrimeCharacteristicRing;

    use super::*;

    type F = BabyBear;

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
        );

        // A constant operand with field element 42.
        let operand = MemOrConstant::Constant(F::from_u64(42));

        // Run `get_value` with an unused memory manager (memory is not needed for constants).
        let memory = MemoryManager::default();

        // It should return the wrapped constant as a MemoryValue::Int.
        let result = ctx.get_value(&operand, &memory).unwrap();
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
        memory
            .memory
            .insert(addr_to_read, expected_val.clone())
            .unwrap();

        // Create a RunContext with that fp.
        let ctx = RunContext::new(
            MemoryAddress {
                segment_index: 0,
                offset: 0,
            }, // dummy pc
            fp,
        );

        // The operand asks to read memory at fp + 2.
        let operand = MemOrConstant::MemoryAfterFp { shift: 2 };

        // Call get_value, which should fetch the value we inserted.
        let result = ctx.get_value(&operand, &memory).unwrap();
        assert_eq!(result, expected_val);
    }

    #[test]
    fn test_get_value_memory_after_fp_uninitialized_memory() {
        let mut memory = MemoryManager::default();

        // Create a segment and set fp to its base.
        let fp = memory.add(); // segment_index = 0, offset = 0

        // We won't insert anything, so all memory is uninitialized.

        // Shift = 1 → fp + 1 points to offset 1 (which is uninitialized).
        let operand: MemOrConstant<F> = MemOrConstant::MemoryAfterFp { shift: 1 };

        // Set up context.
        let ctx = RunContext::new(
            MemoryAddress {
                segment_index: 0,
                offset: 0,
            }, // dummy pc
            fp,
        );

        // Calling get_value should return a VirtualMachineError::MemoryError::UninitializedMemory.
        let err = ctx.get_value(&operand, &memory).unwrap_err();

        match err {
            VirtualMachineError::Memory(MemoryError::UninitializedMemory(addr)) => {
                assert_eq!(addr.segment_index, fp.segment_index);
                assert_eq!(addr.offset, fp.offset + 1);
            }
            other => panic!("Unexpected error: {other:?}"),
        }
    }

    #[test]
    fn test_get_value_from_mem_or_fp_or_constant_is_constant() {
        let ctx = RunContext::new(MemoryAddress::new(0, 0), MemoryAddress::new(1, 0));
        let operand = MemOrFpOrConstant::Constant(F::from_u64(123));
        let memory = MemoryManager::default();
        let result = ctx
            .get_value_from_mem_or_fp_or_constant(&operand, &memory)
            .unwrap();
        assert_eq!(result, MemoryValue::Int(F::from_u64(123)));
    }

    #[test]
    fn test_get_value_from_mem_or_fp_or_constant_is_fp() {
        let fp_addr = MemoryAddress::new(1, 10);
        let ctx = RunContext::new(MemoryAddress::new(0, 0), fp_addr);
        let operand = MemOrFpOrConstant::<F>::Fp;
        let memory = MemoryManager::default();
        let result = ctx
            .get_value_from_mem_or_fp_or_constant(&operand, &memory)
            .unwrap();
        assert_eq!(result, MemoryValue::Address(fp_addr));
    }

    #[test]
    fn test_get_value_from_mem_or_fp_or_constant_is_mem_success() {
        let mut memory = MemoryManager::default();
        let fp = memory.add();
        let addr_to_read = fp.add_usize::<F>(7).unwrap();
        let expected_val = MemoryValue::<F>::Address(MemoryAddress::new(5, 5));
        memory
            .memory
            .insert(addr_to_read, expected_val.clone())
            .unwrap();

        let ctx = RunContext::new(MemoryAddress::new(0, 0), fp);
        let operand = MemOrFpOrConstant::MemoryAfterFp { shift: 7 };
        let result = ctx
            .get_value_from_mem_or_fp_or_constant(&operand, &memory)
            .unwrap();
        assert_eq!(result, expected_val);
    }
}
