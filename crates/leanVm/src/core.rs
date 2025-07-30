use p3_field::{BasedVectorSpace, Field, PrimeField64};
use p3_symmetric::Permutation;

use crate::{
    bytecode::{
        instruction::Instruction,
        operand::{MemOrConstant, MemOrFp, MemOrFpOrConstant},
        operation::Operation,
    },
    constant::{DIMENSION, EF, F},
    context::run_context::RunContext,
    errors::{math::MathError, memory::MemoryError, vm::VirtualMachineError},
    memory::{address::MemoryAddress, manager::MemoryManager, val::MemoryValue},
};

#[derive(Debug)]
pub struct VirtualMachine<PERM16, PERM24> {
    pub(crate) run_context: RunContext,
    pub memory_manager: MemoryManager,
    pub poseidon2_16: PERM16,
    pub poseidon2_24: PERM24,
}

impl<PERM16, PERM24> VirtualMachine<PERM16, PERM24> {
    pub fn new(poseidon2_16: PERM16, poseidon2_24: PERM24) -> Self {
        Self {
            run_context: RunContext::default(),
            memory_manager: MemoryManager::default(),
            poseidon2_16,
            poseidon2_24,
        }
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
        let next_pc = if let Instruction::JumpIfNotZero {
            condition, dest, ..
        } = instruction
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
    pub fn run_instruction(&mut self, instruction: &Instruction) -> Result<(), VirtualMachineError>
    where
        PERM16: Permutation<[F; 2 * DIMENSION]>,
        PERM24: Permutation<[F; 3 * DIMENSION]>,
    {
        // Dispatch to the appropriate execution logic based on the instruction type.
        match instruction {
            // Handle arithmetic operations like ADD and MUL.
            Instruction::Computation {
                operation,
                arg_a,
                arg_b,
                res,
            } => self.execute_computation(operation, arg_a, arg_b, res)?,

            // Handle double-dereference memory operations.
            Instruction::Deref {
                shift_0,
                shift_1,
                res,
            } => self.execute_deref(*shift_0, *shift_1, res)?,

            // The `JumpIfNotZero` instruction has no execution logic; its effects
            // (changing pc and fp) are handled entirely within the register update phase.
            Instruction::JumpIfNotZero { .. } => {}

            // Handle the Poseidon2 (16-element) precompile.
            Instruction::Poseidon2_16 { shift } => self.execute_poseidon2_16(*shift)?,

            // Handle the Poseidon2 (24-element) precompile.
            Instruction::Poseidon2_24 { shift } => self.execute_poseidon2_24(*shift)?,

            // Handle the extension field multiplication precompile.
            Instruction::ExtensionMul { args } => self.execute_extension_mul(*args)?,
        }

        // After the instruction's core logic has been successfully executed,
        // update the pc and fp registers to prepare for the next cycle.
        self.update_registers(instruction)
    }

    /// Executes a computation instruction (`res = arg_a op arg_b`), handling deduction and assertion.
    ///
    /// This function implements the core logic for `ADD` and `MUL` instructions. It follows
    /// a "constraint satisfaction" model:
    ///
    /// 1.  **Deduction:** If exactly one of the three operands (`res`, `arg_a`, `arg_b`) is unknown
    ///     (i.e., its memory cell is uninitialized), the function computes its value from the other
    ///     two and writes it to memory.
    /// 2.  **Assertion:** If all three operands are already known, the function computes `arg_a op arg_b`
    ///     and asserts that it equals the value of `res`.
    fn execute_computation(
        &mut self,
        operation: &Operation,
        arg_a: &MemOrConstant,
        arg_b: &MemOrFp,
        res: &MemOrConstant,
    ) -> Result<(), VirtualMachineError> {
        let memory_manager = &self.memory_manager;
        let run_ctx = &self.run_context;

        let val_a = run_ctx.value_from_mem_or_constant(arg_a, memory_manager);
        let val_b = run_ctx.value_from_mem_or_fp(arg_b, memory_manager);
        let val_res = run_ctx.value_from_mem_or_constant(res, memory_manager);

        match (val_a, val_b, val_res) {
            // Case 1: a OP b = c — compute c
            (Ok(MemoryValue::Int(a)), Ok(MemoryValue::Int(b)), Ok(MemoryValue::Address(addr))) => {
                let c = operation.compute(a, b);
                self.memory_manager.memory.insert(addr, c)?;
            }
            // Case 2: a OP b = c — recover b
            (Ok(MemoryValue::Int(a)), Ok(MemoryValue::Address(addr)), Ok(MemoryValue::Int(c))) => {
                let b = operation
                    .inverse_compute(c, a)
                    .ok_or(MathError::DivisionByZero)?;
                self.memory_manager.memory.insert(addr, b)?;
            }
            // Case 3: a OP b = c — recover a
            (Ok(MemoryValue::Address(addr)), Ok(MemoryValue::Int(b)), Ok(MemoryValue::Int(c))) => {
                let a = operation
                    .inverse_compute(c, b)
                    .ok_or(MathError::DivisionByZero)?;
                self.memory_manager.memory.insert(addr, a)?;
            }
            // Case 4: a OP b = c — assert equality
            (Ok(MemoryValue::Int(a)), Ok(MemoryValue::Int(b)), Ok(MemoryValue::Int(c))) => {
                let computed = operation.compute(a, b);
                if computed != c {
                    return Err(VirtualMachineError::AssertEqFailed {
                        computed: computed.into(),
                        expected: c.into(),
                    });
                }
            }
            _ => return Err(VirtualMachineError::TooManyUnknownOperands),
        }

        Ok(())
    }

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
    fn execute_deref(
        &mut self,
        shift_0: usize,
        shift_1: usize,
        res: &MemOrFpOrConstant,
    ) -> Result<(), VirtualMachineError> {
        // Resolve the `res` operand first to determine which execution path to take.
        //
        // This will either be
        // - a known `Int`,
        // - an `Address` to an unwritten cell.
        let res_lookup_result = self
            .run_context
            .value_from_mem_or_fp_or_constant(res, &self.memory_manager)?;

        // Calculate the address of the first-level pointer, `fp + shift_0`.
        let ptr_shift_0_addr = (self.run_context.fp + shift_0)?;

        // Read the pointer from memory. It must be a `MemoryAddress` type.
        let ptr: MemoryAddress = self.memory_manager.memory.get_as(ptr_shift_0_addr)?;

        // Calculate the final, second-level address: `ptr + shift_1`.
        let ptr_shift_1_addr = (ptr + shift_1)?;

        // Branch execution based on whether `res` was a known value or an unwritten address.
        match res_lookup_result {
            // Case 1: `res` is an unwritten memory location.
            //
            // We deduce its value by reading from the final address.
            MemoryValue::Address(addr) => {
                // Read the value from the final dereferenced address `m[ptr + shift_1]`.
                let value = self
                    .memory_manager
                    .get(ptr_shift_1_addr)
                    .ok_or(MemoryError::UninitializedMemory(ptr_shift_1_addr))?;

                // Write the deduced value into `res`'s memory location.
                self.memory_manager.memory.insert(addr, value)?;
            }
            // Case 2: `res` is a known integer value.
            //
            // We use this value to constrain the memory at the final address.
            MemoryValue::Int(value) => {
                // Write the known `res` value to the final dereferenced address.
                self.memory_manager.memory.insert(ptr_shift_1_addr, value)?;
            }
        }

        Ok(())
    }

    /// Executes the `Poseidon2_16` precompile instruction.
    ///
    /// Reads four pointers from memory starting at `fp + shift`, representing:
    /// - two input vector addresses (`ptr_arg_0`, `ptr_arg_1`)
    /// - two output vector addresses (`ptr_res_0`, `ptr_res_1`)
    ///
    /// Each input is an 8-element vector of `F`. The two inputs are concatenated,
    /// permuted using Poseidon2, and written back to the output locations.
    ///
    /// The operation is: `Poseidon2(m_vec[ptr_0], m_vec[ptr_1]) -> (m_vec[ptr_2], m_vec[ptr_3])`
    fn execute_poseidon2_16(&mut self, shift: usize) -> Result<(), VirtualMachineError>
    where
        PERM16: Permutation<[F; 2 * DIMENSION]>,
    {
        // Read Pointers from Memory
        //
        // The instruction specifies 4 consecutive pointers starting at `fp + shift`.
        let base_ptr_addr = (self.run_context.fp + shift)?;
        let ptrs: [MemoryAddress; 4] = self.memory_manager.memory.get_array_as(base_ptr_addr)?;

        // Convert the `MemoryValue` pointers to `MemoryAddress`.
        let [ptr_arg_0, ptr_arg_1, ptr_res_0, ptr_res_1] = ptrs;

        // Read Input Vectors
        //
        // Read the 8-element vectors from the locations pointed to by `ptr_arg_0` and `ptr_arg_1`.
        let arg0 = self
            .memory_manager
            .memory
            .get_array_as::<F, DIMENSION>(ptr_arg_0)?;
        let arg1 = self
            .memory_manager
            .memory
            .get_array_as::<F, DIMENSION>(ptr_arg_1)?;

        // Perform Hashing
        //
        // Concatenate the two input vectors into a single 16-element array for the permutation.
        let mut state = [arg0, arg1].concat().try_into().unwrap();

        // Apply the Poseidon2 permutation to the state.
        self.poseidon2_16.permute_mut(&mut state);

        // Write Output Vectors
        //
        // Split the permuted state back into two 8-element output vectors.
        let res0: [F; DIMENSION] = state[..DIMENSION].try_into().unwrap();
        let res1: [F; DIMENSION] = state[DIMENSION..].try_into().unwrap();

        // Write the output vectors to the memory locations pointed to by `ptr_res_0` and `ptr_res_1`.
        self.memory_manager.load_data(ptr_res_0, &res0)?;
        self.memory_manager.load_data(ptr_res_1, &res1)?;

        Ok(())
    }

    /// Executes the `Poseidon2_24` precompile instruction.
    ///
    /// Reads six pointers from memory starting at `fp + shift`, representing:
    /// - three input vector addresses (`ptr_arg_0`, `ptr_arg_1`, `ptr_arg_2`)
    /// - three output vector addresses (`ptr_res_0`, `ptr_res_1`, `ptr_res_2`)
    ///
    /// Each input is an 8-element vector of `F`. The three inputs are concatenated into
    /// a single 24-element state, permuted using Poseidon2, and written back to the three
    /// output locations as three 8-element vectors.
    ///
    /// The operation is:
    /// `Poseidon2(m_vec[ptr_0], m_vec[ptr_1], m_vec[ptr_2]) -> (m_vec[ptr_3], m_vec[ptr_4], m_vec[ptr_5])`
    fn execute_poseidon2_24(&mut self, shift: usize) -> Result<(), VirtualMachineError>
    where
        PERM24: Permutation<[F; 3 * DIMENSION]>,
    {
        // Read Pointers from Memory
        //
        // The instruction specifies 6 consecutive pointers starting at `fp + shift`.
        let ptr_addr = (self.run_context.fp + shift)?;
        let ptrs: [MemoryAddress; 6] = self.memory_manager.memory.get_array_as(ptr_addr)?;

        // Convert the raw memory values into memory addresses.
        let [
            ptr_arg_0,
            ptr_arg_1,
            ptr_arg_2,
            ptr_res_0,
            ptr_res_1,
            ptr_res_2,
        ] = ptrs;

        // Read Input Vectors
        //
        // Each is an 8-element array of field elements.
        let arg0 = self
            .memory_manager
            .memory
            .get_array_as::<F, DIMENSION>(ptr_arg_0)?;
        let arg1 = self
            .memory_manager
            .memory
            .get_array_as::<F, DIMENSION>(ptr_arg_1)?;
        let arg2 = self
            .memory_manager
            .memory
            .get_array_as::<F, DIMENSION>(ptr_arg_2)?;

        // Perform Hashing
        //
        // Concatenate the three input vectors into a single 24-element array for the permutation.
        let mut state = [arg0, arg1, arg2].concat().try_into().unwrap();

        // Apply the Poseidon2 permutation to the state.
        self.poseidon2_24.permute_mut(&mut state);

        // Write Output Vectors
        //
        // Split the permuted state back into three 8-element output vectors.
        let res0: [F; DIMENSION] = state[..DIMENSION].try_into().unwrap();
        let res1: [F; DIMENSION] = state[DIMENSION..2 * DIMENSION].try_into().unwrap();
        let res2: [F; DIMENSION] = state[2 * DIMENSION..].try_into().unwrap();

        // Write the output vectors to the memory locations pointed to by the result pointers.
        self.memory_manager.load_data(ptr_res_0, &res0)?;
        self.memory_manager.load_data(ptr_res_1, &res1)?;
        self.memory_manager.load_data(ptr_res_2, &res2)?;

        Ok(())
    }

    /// Executes the `ExtensionMul` instruction.
    ///
    /// Multiplies two extension field elements stored in memory and writes the result back.
    ///
    /// ## Memory Layout
    /// The instruction takes three argument offsets `[a, b, c]` from the frame pointer `fp`:
    ///
    /// - `fp + a`: address of a pointer to the first operand
    /// - `fp + b`: address of a pointer to the second operand
    /// - `fp + c`: address of a pointer to the output location
    ///
    /// The multiplication is:
    ///
    /// ```text
    /// m_vec[ptr_out] = EF::from(m_vec[ptr_lhs]) * EF::from(m_vec[ptr_rhs])
    /// ```
    ///
    /// where `ptr_lhs`, `ptr_rhs`, and `ptr_out` are memory addresses stored at `fp + args[0..=2]`.
    fn execute_extension_mul(&mut self, args: [usize; 3]) -> Result<(), VirtualMachineError> {
        // Get the frame pointer.
        let fp = self.run_context.fp;

        // Read the memory addresses where the operands and result will reside.
        let ptr_lhs: MemoryAddress = self.memory_manager.memory.get_as((fp + args[0])?)?;
        let ptr_rhs: MemoryAddress = self.memory_manager.memory.get_as((fp + args[1])?)?;
        let ptr_out: MemoryAddress = self.memory_manager.memory.get_as((fp + args[2])?)?;

        // Load the `[F; EF::DIMENSION]` input arrays from memory and convert them into EF elements.
        let lhs = EF::from_basis_coefficients_slice(
            &self
                .memory_manager
                .memory
                .get_array_as::<F, DIMENSION>(ptr_lhs)?,
        )
        .unwrap();

        let rhs = EF::from_basis_coefficients_slice(
            &self
                .memory_manager
                .memory
                .get_array_as::<F, DIMENSION>(ptr_rhs)?,
        )
        .unwrap();

        // Perform the field multiplication in the extension field.
        let product = lhs * rhs;

        // Write the result converted back into `[F; EF::DIMENSION]` to memory.
        let result_coeffs: &[F] = product.as_basis_coefficients_slice();
        self.memory_manager.load_data(ptr_out, result_coeffs)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use p3_field::PrimeCharacteristicRing;
    use p3_koala_bear::Poseidon2KoalaBear;
    use rand::{SeedableRng, rngs::StdRng};

    use super::*;
    use crate::{
        bytecode::{operand::MemOrConstant, operation::Operation},
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
        let instruction = Instruction::Computation {
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
        let mut vm = setup_vm(pc, fp, &[((fp + 1).unwrap(), MemoryValue::Int(F::ZERO))]);
        // Define a JNZ instruction where the condition points to the zero value.
        let instruction = Instruction::JumpIfNotZero {
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
                ((fp + 1).unwrap(), MemoryValue::Int(F::from_u64(42))),
                // The destination address for the jump.
                ((fp + 2).unwrap(), MemoryValue::Address(jump_target)),
            ],
        );
        // Define a JNZ instruction pointing to the condition and destination.
        let instruction = Instruction::JumpIfNotZero {
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
                (fp + 1).unwrap(),
                MemoryValue::Address(MemoryAddress::new(8, 8)),
            )],
        );
        // Define a JNZ instruction where the condition points to the address.
        let instruction = Instruction::JumpIfNotZero {
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
        let instruction = Instruction::JumpIfNotZero {
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
            &[((fp + 3).unwrap(), MemoryValue::Address(new_fp))],
        );
        // Define a JNZ instruction where `updated_fp` points to the new address in memory.
        let instruction = Instruction::JumpIfNotZero {
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
            &[((fp + 3).unwrap(), MemoryValue::Int(F::from_u64(99)))],
        );
        // Define a JNZ instruction where `updated_fp` points to this integer value.
        let instruction = Instruction::JumpIfNotZero {
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
