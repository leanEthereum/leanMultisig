use p3_field::PrimeField64;

use crate::{
    bytecode::{instruction::Instruction, operand::MemOrFp},
    context::run_context::RunContext,
    errors::{memory::MemoryError, vm::VirtualMachineError},
    memory::manager::MemoryManager,
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
                self.run_context.pc().add_usize(1)?
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
            self.run_context.pc().add_usize(1)?
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
                    let addr = self.run_context.fp().add_usize(*shift)?;
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

    /// Updates the program counter and frame pointer based on the executed instruction.
    fn update_registers<F>(
        &mut self,
        instruction: &Instruction<F>,
    ) -> Result<(), VirtualMachineError<F>>
    where
        F: PrimeField64,
    {
        // Update the program counter.
        self.update_pc(instruction)?;
        // Update the frame pointer.
        self.update_fp(instruction)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use p3_baby_bear::BabyBear;
    use p3_field::PrimeCharacteristicRing;

    use super::*;
    use crate::{
        bytecode::{operand::MemOrConstant, operation::Operation},
        memory::{address::MemoryAddress, val::MemoryValue},
    };

    type F = BabyBear;

    /// Creates and configures a `VirtualMachine` instance for testing purposes.
    ///
    /// This function streamlines the setup process for tests by initializing the VM
    /// with a specific state, including
    /// - the program counter (`pc`),
    /// - the frame pointer (`fp`),
    /// - any required initial memory values.
    fn setup_vm(
        pc: MemoryAddress,
        fp: MemoryAddress,
        initial_memory: &[(MemoryAddress, MemoryValue<F>)],
    ) -> VirtualMachine {
        // Create a new VM with default values.
        let mut vm = VirtualMachine::default();
        // Set the initial program counter and frame pointer.
        vm.run_context.pc = pc;
        vm.run_context.fp = fp;
        // Iterate through the provided initial memory layout.
        for (addr, val) in initial_memory {
            // Ensure enough memory segments are allocated to accommodate the address.
            while vm.memory_manager.num_segments() <= addr.segment_index {
                vm.memory_manager.add();
            }
            // Insert the value at the specified address, panicking on failure for test simplicity.
            vm.memory_manager.memory.insert(*addr, val.clone()).unwrap();
        }
        // Return the fully configured VM.
        vm
    }

    #[test]
    fn test_update_pc_for_non_jnz_instruction() {
        // Setup: Initialize a VM with the PC at (0, 5).
        let mut vm = setup_vm(MemoryAddress::new(0, 5), MemoryAddress::new(1, 0), &[]);
        // Define a non-jump instruction (e.g., a computation).
        let instruction = Instruction::Computation::<F> {
            operation: Operation::Add,
            arg_a: MemOrConstant::Constant(F::ONE),
            arg_b: MemOrFp::Fp,
            res: MemOrConstant::MemoryAfterFp { shift: 0 },
        };
        // Execute: Update the PC based on this instruction.
        vm.update_pc(&instruction).unwrap();
        // Verify: The PC should increment by 1, as it's not a JNZ instruction.
        assert_eq!(vm.run_context.pc, MemoryAddress::new(0, 6));
    }

    #[test]
    fn test_update_pc_jnz_condition_zero() {
        // Setup: Initialize PC and FP registers.
        let pc = MemoryAddress::new(0, 10);
        let fp = MemoryAddress::new(1, 5);
        // Pre-load memory with a zero value at the address `fp + 1`, which will be our condition.
        let mut vm = setup_vm(
            pc,
            fp,
            &[(fp.add_usize::<F>(1).unwrap(), MemoryValue::Int(F::ZERO))],
        );
        // Define a JNZ instruction where the condition points to the zero value.
        let instruction = Instruction::JumpIfNotZero::<F> {
            condition: MemOrConstant::MemoryAfterFp { shift: 1 },
            dest: MemOrConstant::Constant(F::from_u64(99)), // This destination should be ignored.
            updated_fp: MemOrFp::Fp,
        };
        // Execute: Update the PC.
        vm.update_pc(&instruction).unwrap();
        // Verify: Since the condition is zero, the jump is not taken, and the PC increments by 1.
        assert_eq!(vm.run_context.pc, MemoryAddress::new(0, 11));
    }

    #[test]
    fn test_update_pc_jnz_condition_nonzero_jumps() {
        // Setup: Initialize PC and FP registers.
        let pc = MemoryAddress::new(0, 10);
        let fp = MemoryAddress::new(1, 5);
        // Define the target address for the jump.
        let jump_target = MemoryAddress::new(2, 20);
        // Pre-load memory with a non-zero condition value and the jump target address.
        let mut vm = setup_vm(
            pc,
            fp,
            &[
                // The condition value (non-zero).
                (
                    fp.add_usize::<F>(1).unwrap(),
                    MemoryValue::Int(F::from_u64(42)),
                ),
                // The destination address for the jump.
                (
                    fp.add_usize::<F>(2).unwrap(),
                    MemoryValue::Address(jump_target),
                ),
            ],
        );
        // Define a JNZ instruction pointing to the condition and destination.
        let instruction = Instruction::JumpIfNotZero::<F> {
            condition: MemOrConstant::MemoryAfterFp { shift: 1 },
            dest: MemOrConstant::MemoryAfterFp { shift: 2 },
            updated_fp: MemOrFp::Fp,
        };
        // Execute: Update the PC.
        vm.update_pc(&instruction).unwrap();
        // Verify: Since the condition is non-zero, the PC should be updated to the jump target.
        assert_eq!(vm.run_context.pc, jump_target);
    }

    #[test]
    fn test_update_pc_jnz_condition_is_address_fails() {
        // Setup: Initialize PC and FP.
        let pc = MemoryAddress::new(0, 10);
        let fp = MemoryAddress::new(1, 5);
        // Pre-load memory with an Address where an integer condition is expected.
        let mut vm = setup_vm(
            pc,
            fp,
            &[(
                fp.add_usize::<F>(1).unwrap(),
                MemoryValue::Address(MemoryAddress::new(8, 8)),
            )],
        );
        // Define a JNZ instruction where the condition points to the address.
        let instruction = Instruction::JumpIfNotZero::<F> {
            condition: MemOrConstant::MemoryAfterFp { shift: 1 },
            dest: MemOrConstant::Constant(F::ONE),
            updated_fp: MemOrFp::Fp,
        };
        // Execute: Attempt to update the PC.
        let result = vm.update_pc(&instruction);
        // Verify: The operation should fail because a condition must be an integer, not an address.
        assert!(matches!(
            result,
            Err(VirtualMachineError::Memory(MemoryError::ExpectedInteger))
        ));
    }

    #[test]
    fn test_update_fp_jnz_regular_update() {
        // Setup: Initialize the FP to a known address.
        let fp = MemoryAddress::new(1, 5);
        let mut vm = setup_vm(MemoryAddress::new(0, 0), fp, &[]);
        // Define a JNZ instruction that specifies the FP should not change (`MemOrFp::Fp`).
        let instruction = Instruction::JumpIfNotZero::<F> {
            condition: MemOrConstant::Constant(F::ONE),
            dest: MemOrConstant::Constant(F::ONE),
            updated_fp: MemOrFp::Fp,
        };
        // Execute: Update the FP.
        vm.update_fp(&instruction).unwrap();
        // Verify: The FP should remain unchanged.
        assert_eq!(vm.run_context.fp, fp);
    }

    #[test]
    fn test_update_fp_jnz_dst_update() {
        // Setup: Initialize the FP and define a new address for it to be updated to.
        let fp = MemoryAddress::new(1, 5);
        let new_fp = MemoryAddress::new(2, 0);
        // Pre-load memory with the new FP address at `fp + 3`.
        let mut vm = setup_vm(
            MemoryAddress::new(0, 0),
            fp,
            &[(fp.add_usize::<F>(3).unwrap(), MemoryValue::Address(new_fp))],
        );
        // Define a JNZ instruction where `updated_fp` points to the new address in memory.
        let instruction = Instruction::JumpIfNotZero::<F> {
            condition: MemOrConstant::Constant(F::ONE),
            dest: MemOrConstant::Constant(F::ONE),
            updated_fp: MemOrFp::MemoryAfterFp { shift: 3 },
        };
        // Execute: Update the FP.
        vm.update_fp(&instruction).unwrap();
        // Verify: The FP should be updated to the new address.
        assert_eq!(vm.run_context.fp, new_fp);
    }

    #[test]
    fn test_update_fp_jnz_dst_is_int_fails() {
        // Setup: Initialize the FP.
        let fp = MemoryAddress::new(1, 5);
        // Pre-load memory with an integer value where a new FP address is expected.
        let mut vm = setup_vm(
            MemoryAddress::new(0, 0),
            fp,
            &[(
                fp.add_usize::<F>(3).unwrap(),
                MemoryValue::Int(F::from_u64(99)),
            )],
        );
        // Define a JNZ instruction where `updated_fp` points to this integer value.
        let instruction = Instruction::JumpIfNotZero::<F> {
            condition: MemOrConstant::Constant(F::ONE),
            dest: MemOrConstant::Constant(F::ONE),
            updated_fp: MemOrFp::MemoryAfterFp { shift: 3 },
        };
        // Execute: Attempt to update the FP.
        let result = vm.update_fp(&instruction);
        // Verify: The operation should fail because the new FP value must be an address, not an integer.
        assert!(matches!(
            result,
            Err(VirtualMachineError::Memory(
                MemoryError::ExpectedMemoryAddress
            ))
        ));
    }
}
