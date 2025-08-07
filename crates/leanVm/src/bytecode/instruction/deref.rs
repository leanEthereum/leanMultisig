use crate::{
    bytecode::operand::MemOrFpOrConstant,
    context::run_context::RunContext,
    errors::{memory::MemoryError, vm::VirtualMachineError},
    memory::{address::MemoryAddress, manager::MemoryManager, val::MemoryValue},
};

/// Performs a double-dereference memory access: `res = m[m[fp + shift_0] + shift_1]`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DerefInstruction {
    /// The offset from `fp` for the first memory access, which yields a pointer.
    pub shift_0: usize,
    /// The offset added to the pointer from the first access to get the final address.
    pub shift_1: usize,
    /// The value that the result of the double dereference must be equal to.
    pub res: MemOrFpOrConstant,
}

impl DerefInstruction {
    /// Executes the `DEREF` instruction: `res = m[m[fp + shift_0] + shift_1]`.
    ///
    /// It operates using a constraint satisfaction model with two primary modes:
    ///
    /// 1.  **Deduction of `res`**: If the `res` operand points to an unwritten memory
    ///     location, this function performs the double-dereference to find the final
    ///     value and writes it into `res`'s location.
    ///
    /// 2.  **Constraint of `m[...]`**: If `res` holds a known value, that value is
    ///     written to the final dereferenced address. The underlying memory model
    ///     ensures this write is consistent, effectively asserting that
    ///     `m[m[...]]` must equal the known `res` value.
    pub fn execute(
        &self,
        run_context: &RunContext,
        memory_manager: &mut MemoryManager,
    ) -> Result<(), VirtualMachineError> {
        // Resolve the `res` operand first to determine which execution path to take.
        //
        // This will either be
        // - a known `Int`,
        // - an `Address` to an unwritten cell.
        let res_lookup_result =
            run_context.value_from_mem_or_fp_or_constant(&self.res, memory_manager)?;

        // Calculate the address of the first-level pointer, `fp + shift_0`.
        let ptr_shift_0_addr = (run_context.fp + self.shift_0)?;

        // Read the pointer from memory. It must be a `MemoryAddress` type.
        let ptr: MemoryAddress = memory_manager.memory.get_as(ptr_shift_0_addr)?;

        // Calculate the final, second-level address: `ptr + shift_1`.
        let ptr_shift_1_addr = (ptr + self.shift_1)?;

        // Branch execution based on whether `res` was a known value or an unwritten address.
        match res_lookup_result {
            // Case 1: `res` is an unwritten memory location.
            //
            // We deduce its value by reading from the final address.
            MemoryValue::Address(addr) => {
                // Read the value from the final dereferenced address `m[ptr + shift_1]`.
                let value = memory_manager
                    .get(ptr_shift_1_addr)
                    .ok_or(MemoryError::UninitializedMemory(ptr_shift_1_addr))?;

                // Write the deduced value into `res`'s memory location.
                memory_manager.memory.insert(addr, value)?;
            }
            // Case 2: `res` is a known integer value.
            //
            // We use this value to constrain the memory at the final address.
            MemoryValue::Int(value) => {
                // Write the known `res` value to the final dereferenced address.
                memory_manager.memory.insert(ptr_shift_1_addr, value)?;
            }
        }

        Ok(())
    }
}
