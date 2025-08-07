use p3_field::{Field, PrimeCharacteristicRing, PrimeField64};
use p3_symmetric::Permutation;

use crate::{
    bytecode::{
        instruction::{Instruction, jump::JumpIfNotZeroInstruction},
        operand::MemOrFp,
        program::Program,
    },
    constant::{
        CODE_SEGMENT, DIMENSION, F, POSEIDON_16_NULL_HASH_PTR, POSEIDON_24_NULL_HASH_PTR,
        PUBLIC_INPUT_START, ZERO_VEC_PTR,
    },
    context::run_context::RunContext,
    errors::{memory::MemoryError, vm::VirtualMachineError},
    memory::{address::MemoryAddress, manager::MemoryManager},
};

#[derive(Debug)]
pub struct VirtualMachine<Perm16, Perm24> {
    pub(crate) run_context: RunContext,
    pub memory_manager: MemoryManager,
    pub poseidon2_16: Perm16,
    pub poseidon2_24: Perm24,
    pub(crate) program: Program,
}

impl<Perm16, Perm24> VirtualMachine<Perm16, Perm24>
where
    Perm16: Permutation<[F; 2 * DIMENSION]>,
    Perm24: Permutation<[F; 3 * DIMENSION]>,
{
    pub fn new(poseidon2_16: Perm16, poseidon2_24: Perm24) -> Self {
        Self {
            run_context: RunContext::default(),
            memory_manager: MemoryManager::default(),
            program: Program::default(),
            poseidon2_16,
            poseidon2_24,
        }
    }

    /// Initializes the virtual machine with a given program.
    ///
    /// This function performs all the necessary setup before execution:
    ///
    /// - Allocates the required memory segments
    /// - Loads public and private inputs into stack memory
    /// - Fills in convention-based memory slots (e.g., zero vector, null hashes)
    /// - Computes and aligns allocation pointers
    /// - Sets up the initial execution context (program counter, frame pointer, etc.)
    pub fn setup(
        &mut self,
        program: Program,
        no_vec_runtime_memory: usize,
    ) -> Result<(), VirtualMachineError> {
        // Save the program internally.
        self.program = program;

        // Extract the public and private inputs from the program.
        let public_input = &self.program.public_input;
        let private_input = &self.program.private_input;

        // Allocate required memory segments: PUBLIC, STACK, VEC, CODE.
        // We ensure all necessary segments are present.
        while self.memory_manager.num_segments() <= CODE_SEGMENT {
            self.memory_manager.add();
        }

        // Convention-Based Memory Initialization

        // Write [0; DIMENSION] to the vector memory at ZERO_VEC_PTR.
        self.memory_manager
            .load_data(ZERO_VEC_PTR, &[F::ZERO; DIMENSION])?;

        // Write Poseidon2([0; 16]) to POSEIDON_16_NULL_HASH_PTR.
        let hash16 = self.poseidon2_16.permute([F::ZERO; DIMENSION * 2]);
        self.memory_manager
            .load_data(POSEIDON_16_NULL_HASH_PTR, &hash16)?;

        // Write the last 8 elements of Poseidon2([0; 24]) to POSEIDON_24_NULL_HASH_PTR.
        let hash24 = self.poseidon2_24.permute([F::ZERO; DIMENSION * 3]);
        self.memory_manager
            .load_data(POSEIDON_24_NULL_HASH_PTR, &hash24[16..])?;

        // Load Public Inputs

        // Place public input values starting at PUBLIC_INPUT_START in the public data segment.
        self.memory_manager
            .load_data(PUBLIC_INPUT_START, public_input)?;

        // Compute the initial `fp` (frame pointer) just after the public inputs.
        let mut fp = (PUBLIC_INPUT_START + public_input.len())?;
        // Align the `fp` offset to the next power of two.
        fp.offset = fp.offset.next_power_of_two();

        // Load Private Inputs

        // Write private inputs starting at the aligned `fp`.
        self.memory_manager.load_data(fp, private_input)?;

        // Advance `fp` past the private inputs.
        fp.offset += private_input.len();
        // Ensure `fp` is aligned to `DIMENSION` for vector operations.
        fp.offset = fp.offset.next_multiple_of(DIMENSION);

        // Compute Allocation Pointers

        // Compute the initial allocation pointer for stack memory.
        let initial_ap = (fp + self.program.bytecode.starting_frame_memory)?;

        // Compute the vectorized allocation pointer, skipping past the non-vector memory.
        let mut initial_ap_vec = (initial_ap + no_vec_runtime_memory)?;
        // Align the vector allocation to the next multiple of `DIMENSION`.
        initial_ap_vec.offset = initial_ap_vec.offset.next_multiple_of(DIMENSION) / DIMENSION;

        // Set Initial Registers

        // Set the program counter to the start of the code segment.
        self.run_context.pc = MemoryAddress::new(CODE_SEGMENT, 0);

        // Set the frame pointer to the aligned `fp`.
        self.run_context.fp = fp;

        // Set the allocation pointer for non-vector memory.
        self.run_context.ap = initial_ap;

        // Set the allocation pointer for vector memory (in vector units, not field elements).
        self.run_context.ap_vectorized = initial_ap_vec;

        Ok(())
    }

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
    pub fn update_pc(&mut self, instruction: &Instruction) -> Result<(), VirtualMachineError>
    where
        F: PrimeField64,
    {
        // Determine the next program counter `pc` by checking if the instruction is a conditional jump.
        let next_pc =
            if let Instruction::JumpIfNotZero(JumpIfNotZeroInstruction {
                condition, dest, ..
            }) = instruction
            {
                // For a `JumpIfNotZero` instruction, resolve the `condition` operand from memory or constants.
                // This will return an error if the memory location is uninitialized.
                let condition_val = self
                    .run_context
                    .value_from_mem_or_constant(condition, &self.memory_manager)?;

                // A jump condition must be a field element.
                let f: F = condition_val.try_into()?;

                if f.is_zero() {
                    // **Condition is zero**: The jump is not taken. Advance the `pc` by one.
                    (*self.run_context.pc() + 1)?
                } else {
                    // **Condition is non-zero**: Execute the jump.
                    //
                    // First, resolve the `dest` operand to get the target address value.
                    let dest_val = self
                        .run_context
                        .value_from_mem_or_constant(dest, &self.memory_manager)?;

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
    pub fn update_fp(&mut self, instruction: &Instruction) -> Result<(), VirtualMachineError>
    where
        F: PrimeField64,
    {
        if let Instruction::JumpIfNotZero(jump_if_not_zero) = instruction {
            let new_fp = match jump_if_not_zero.updated_fp {
                // The instruction specifies keeping the same `fp`.
                MemOrFp::Fp => self.run_context.fp,
                // The instruction specifies updating `fp` to a value from memory.
                MemOrFp::MemoryAfterFp { shift } => {
                    let addr = (*self.run_context.fp() + shift)?;
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
    fn update_registers(&mut self, instruction: &Instruction) -> Result<(), VirtualMachineError>
    where
        F: PrimeField64,
    {
        // Update the program counter.
        self.update_pc(instruction)?;
        // Update the frame pointer.
        self.update_fp(instruction)?;

        Ok(())
    }

    /// Executes a single instruction, forming one step of the VM's execution cycle.
    ///
    /// This function is the engine of the virtual machine. It orchestrates the two main phases
    /// of a single step: execution and register update.
    ///
    /// 1.  **Execution:** It first matches on the `instruction` variant to dispatch to the appropriate
    ///     helper method. These helpers are responsible for fetching operands, performing the instruction's core logic, and
    ///     verifying any required assertions (e.g., that a computed value matches an expected one).
    ///
    /// 2.  **Register Update:** If the execution phase completes successfully, this function then
    ///     calls `update_registers` to advance the program counter (`pc`) and frame pointer (`fp`)
    ///     to prepare for the next instruction.
    pub fn run_instruction(
        &mut self,
        instruction: &Instruction,
    ) -> Result<(), VirtualMachineError> {
        // Execute the instruction.
        instruction.execute(
            &self.run_context,
            &mut self.memory_manager,
            &self.poseidon2_16,
            &self.poseidon2_24,
        )?;

        // After the instruction's core logic has been successfully executed,
        // update the pc and fp registers to prepare for the next cycle.
        self.update_registers(instruction)
    }
}

#[cfg(test)]
mod tests {
    use p3_field::PrimeCharacteristicRing;
    use p3_koala_bear::Poseidon2KoalaBear;
    use rand::{SeedableRng, rngs::StdRng};

    use super::*;
    use crate::{
        bytecode::{
            instruction::{computation::ComputationInstruction, jump::JumpIfNotZeroInstruction},
            operand::MemOrConstant,
            operation::Operation,
        },
        memory::{address::MemoryAddress, val::MemoryValue},
    };

    type Poseidon16 = Poseidon2KoalaBear<16>;
    type Poseidon24 = Poseidon2KoalaBear<24>;

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
        initial_memory: &[(MemoryAddress, MemoryValue)],
    ) -> VirtualMachine<Poseidon16, Poseidon24> {
        let poseidon_16 = Poseidon16::new_from_rng_128(&mut StdRng::seed_from_u64(0));
        let poseidon_24 = Poseidon24::new_from_rng_128(&mut StdRng::seed_from_u64(0));

        // Create a new VM with default values.
        let mut vm = VirtualMachine::new(poseidon_16, poseidon_24);
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
            vm.memory_manager.memory.insert(*addr, *val).unwrap();
        }
        // Return the fully configured VM.
        vm
    }

    #[test]
    fn test_update_pc_for_non_jnz_instruction() {
        // Setup: Initialize a VM with the PC at (0, 5).
        let mut vm = setup_vm(MemoryAddress::new(0, 5), MemoryAddress::new(1, 0), &[]);
        // Define a non-jump instruction (e.g., a computation).
        let instruction = Instruction::Computation(ComputationInstruction {
            operation: Operation::Add,
            arg_a: MemOrConstant::Constant(F::ONE),
            arg_b: MemOrFp::Fp,
            res: MemOrConstant::MemoryAfterFp { shift: 0 },
        });
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
        let mut vm = setup_vm(pc, fp, &[((fp + 1).unwrap(), MemoryValue::Int(F::ZERO))]);
        // Define a JNZ instruction where the condition points to the zero value.
        let instruction = Instruction::JumpIfNotZero(JumpIfNotZeroInstruction {
            condition: MemOrConstant::MemoryAfterFp { shift: 1 },
            dest: MemOrConstant::Constant(F::from_u64(99)), // This destination should be ignored.
            updated_fp: MemOrFp::Fp,
        });
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
                ((fp + 1).unwrap(), MemoryValue::Int(F::from_u64(42))),
                // The destination address for the jump.
                ((fp + 2).unwrap(), MemoryValue::Address(jump_target)),
            ],
        );
        // Define a JNZ instruction pointing to the condition and destination.
        let instruction = Instruction::JumpIfNotZero(JumpIfNotZeroInstruction {
            condition: MemOrConstant::MemoryAfterFp { shift: 1 },
            dest: MemOrConstant::MemoryAfterFp { shift: 2 },
            updated_fp: MemOrFp::Fp,
        });
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
                (fp + 1).unwrap(),
                MemoryValue::Address(MemoryAddress::new(8, 8)),
            )],
        );
        // Define a JNZ instruction where the condition points to the address.
        let instruction = Instruction::JumpIfNotZero(JumpIfNotZeroInstruction {
            condition: MemOrConstant::MemoryAfterFp { shift: 1 },
            dest: MemOrConstant::Constant(F::ONE),
            updated_fp: MemOrFp::Fp,
        });
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
        let instruction = Instruction::JumpIfNotZero(JumpIfNotZeroInstruction {
            condition: MemOrConstant::Constant(F::ONE),
            dest: MemOrConstant::Constant(F::ONE),
            updated_fp: MemOrFp::Fp,
        });
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
            &[((fp + 3).unwrap(), MemoryValue::Address(new_fp))],
        );
        // Define a JNZ instruction where `updated_fp` points to the new address in memory.
        let instruction = Instruction::JumpIfNotZero(JumpIfNotZeroInstruction {
            condition: MemOrConstant::Constant(F::ONE),
            dest: MemOrConstant::Constant(F::ONE),
            updated_fp: MemOrFp::MemoryAfterFp { shift: 3 },
        });
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
            &[((fp + 3).unwrap(), MemoryValue::Int(F::from_u64(99)))],
        );
        // Define a JNZ instruction where `updated_fp` points to this integer value.
        let instruction = Instruction::JumpIfNotZero(JumpIfNotZeroInstruction {
            condition: MemOrConstant::Constant(F::ONE),
            dest: MemOrConstant::Constant(F::ONE),
            updated_fp: MemOrFp::MemoryAfterFp { shift: 3 },
        });
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
