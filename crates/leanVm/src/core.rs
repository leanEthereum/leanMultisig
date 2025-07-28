use p3_field::PrimeField64;

use crate::{
    context::run_context::RunContext,
    errors::{memory::MemoryError, vm::VirtualMachineError},
    memory::manager::MemoryManager,
    types::instruction::{Instruction, MemOrFp},
};

#[derive(Debug, Default)]
pub struct VirtualMachine {
    pub(crate) run_context: RunContext,
    pub memory_manager: MemoryManager,
}

impl VirtualMachine {
    /// Advances the program counter (`pc`) to the next instruction.
    ///
    /// This function embodies the control flow logic of the zkVM. For most instructions,
    /// it performs a regular increment of the **`pc`**. However, for the `JumpIfNotZero`
    /// instruction (`JUZ`), it implements conditional branching.
    ///
    /// ### `JumpIfNotZero` Logic
    ///
    /// When a `JumpIfNotZero` instruction is processed:
    /// 1.  The `condition` operand is resolved to a field element.
    /// 2.  If this value is **zero**, the program continues sequentially, and the **`pc`** is incremented by 1.
    /// 3.  If the value is **non-zero**, a jump is executed. The `dest` operand is resolved to find the
    ///     target `MemoryAddress`, which then becomes the new **`pc`**.
    pub fn update_pc<F>(
        &mut self,
        instruction: &Instruction<F>,
    ) -> Result<(), VirtualMachineError<F>>
    where
        F: PrimeField64,
    {
        // Determine the next program counter `pc` by checking if the instruction is a conditional jump.
        let next_pc = if let Instruction::JumpIfNotZero {
            condition, dest, ..
        } = instruction
        {
            // For a `JumpIfNotZero` instruction, resolve the `condition` operand from memory or constants.
            // This will return an error if the memory location is uninitialized.
            let condition_val = self
                .run_context
                .get_value(condition, &self.memory_manager)?;

            // A jump condition must be a field element.
            let is_zero = condition_val.to_f()?.is_zero();

            if is_zero {
                // **Condition is zero**: The jump is not taken. Advance the `pc` by one.
                (*self.run_context.pc() + 1)?
            } else {
                // **Condition is non-zero**: Execute the jump.
                //
                // First, resolve the `dest` operand to get the target address value.
                let dest_val = self.run_context.get_value(dest, &self.memory_manager)?;

                // The resolved destination value must be a valid address.
                //
                // Convert it and set it as the new `pc`.
                dest_val.try_into()?
            }
        } else {
            // For any instruction other than `JumpIfNotZero`, advance the `pc` by one.
            (*self.run_context.pc() + 1)?
        };

        // Update the virtual machine's program counter with the calculated next address.
        self.run_context.pc = next_pc;
        Ok(())
    }

    /// Updates the frame pointer (`fp`) based on the executed instruction.
    pub fn update_fp<F>(
        &mut self,
        instruction: &Instruction<F>,
    ) -> Result<(), VirtualMachineError<F>>
    where
        F: PrimeField64,
    {
        if let Instruction::JumpIfNotZero { updated_fp, .. } = instruction {
            let new_fp = match updated_fp {
                // The instruction specifies keeping the same `fp`.
                MemOrFp::Fp => self.run_context.fp,
                // The instruction specifies updating `fp` to a value from memory.
                MemOrFp::MemoryAfterFp { shift } => {
                    let addr = (*self.run_context.fp() + *shift)?;
                    let value = self
                        .memory_manager
                        .get(addr)
                        .ok_or(MemoryError::UninitializedMemory(addr))?;

                    // The fetched value must be a valid memory address to become the new `fp`.
                    value.try_into()?
                }
            };
            self.run_context.fp = new_fp;
        }

        // For the other instructions, we do nothing for now.
        //
        // To be checked in the future.

        Ok(())
    }
}
