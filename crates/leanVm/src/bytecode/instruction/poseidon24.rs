use p3_field::BasedVectorSpace;
use p3_symmetric::Permutation;

use crate::{
    bytecode::operand::{MemOrConstant, MemOrFp},
    constant::{DIMENSION, F},
    context::run_context::RunContext,
    errors::vm::VirtualMachineError,
    memory::{address::MemoryAddress, manager::MemoryManager},
    witness::poseidon::WitnessPoseidon24,
};

/// Poseidon2 permutation over 24 field elements (3 inputs, 3 outputs).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Poseidon2_24Instruction {
    /// A pointer to the first two 8-element input vectors.
    pub arg_a: MemOrConstant,
    /// A pointer to the third 8-element input vector.
    pub arg_b: MemOrConstant,
    /// A pointer to the location of the third 8-element output vector.
    pub res: MemOrFp,
}

impl Poseidon2_24Instruction {
    /// Executes the `Poseidon2_24` precompile instruction.
    ///
    /// This function resolves pointers from its operands to find the memory locations for
    /// three 8-element input vectors and one 8-element output vector. It reads the inputs,
    /// concatenates them, applies the permutation, and writes the third resulting vector
    /// back to its designated output location.
    pub fn execute<Perm>(
        &self,
        run_context: &RunContext,
        memory_manager: &mut MemoryManager,
        perm: &Perm,
    ) -> Result<(), VirtualMachineError>
    where
        Perm: Permutation<[F; 3 * DIMENSION]>,
    {
        // Pointer Resolution
        //
        // Resolve the pointer to the first block of two input vectors from the `arg_a` operand.
        let ptr_arg_a: MemoryAddress = run_context
            .value_from_mem_or_constant(&self.arg_a, memory_manager)?
            .try_into()?;
        // The second input vector is located immediately after the first one.
        let ptr_arg_b = (ptr_arg_a + 1)?;
        // Resolve the pointer to the third input vector from the `arg_b` operand.
        let ptr_arg_c: MemoryAddress = run_context
            .value_from_mem_or_constant(&self.arg_b, memory_manager)?
            .try_into()?;
        // Resolve the pointer to the third output vector from the `res` operand.
        let ptr_res: MemoryAddress = run_context
            .value_from_mem_or_fp(&self.res, memory_manager)?
            .try_into()?;

        // Data Reading
        //
        // Read the first 8-element input vector from memory.
        let arg0 = memory_manager
            .memory
            .get_array_as::<F, DIMENSION>(ptr_arg_a)?;
        // Read the second 8-element input vector from memory.
        let arg1 = memory_manager
            .memory
            .get_array_as::<F, DIMENSION>(ptr_arg_b)?;
        // Read the third 8-element input vector from memory.
        let arg2 = memory_manager
            .memory
            .get_array_as::<F, DIMENSION>(ptr_arg_c)?;

        // Hashing
        //
        // Concatenate the three input vectors into a single 24-element array for the permutation.
        let mut state = [arg0, arg1, arg2].concat().try_into().unwrap();
        // Apply the Poseidon2 permutation to the state.
        perm.permute_mut(&mut state);

        // Data Writing
        //
        // Extract the last 8 elements of the permuted state, which is the result.
        let res: [F; DIMENSION] = state[2 * DIMENSION..].try_into().unwrap();
        // Write the result vector to the memory location pointed to by the result pointer.
        memory_manager.load_data(ptr_res, &res)?;

        Ok(())
    }

    /// Generates the witness for a `Poseidon2_24` instruction execution.
    pub fn generate_witness(
        &self,
        cycle: usize,
        run_context: &RunContext,
        memory_manager: &MemoryManager,
    ) -> Result<WitnessPoseidon24, VirtualMachineError> {
        // Pointer Resolution
        //
        // Resolve the pointer to the first block of two input vectors from the `arg_a` operand.
        let addr_input_a: MemoryAddress = run_context
            .value_from_mem_or_constant(&self.arg_a, memory_manager)?
            .try_into()?;
        // Resolve the pointer to the third input vector from the `arg_b` operand.
        let addr_input_b: MemoryAddress = run_context
            .value_from_mem_or_constant(&self.arg_b, memory_manager)?
            .try_into()?;
        // Resolve the pointer to the third output vector from the `res` operand.
        let addr_output: MemoryAddress = run_context
            .value_from_mem_or_fp(&self.res, memory_manager)?
            .try_into()?;

        // Data Reading
        //
        // Read the first two input vectors (a slice of 2 EF elements, total 16 F elements) from memory.
        let value_a = memory_manager
            .memory
            .get_vectorized_slice_extension(addr_input_a, 2)?;
        // Read the third input vector (a single EF element, total 8 F elements) from memory.
        let value_b = memory_manager.memory.get_extension(addr_input_b)?;
        // Read the third output vector (a single EF element, total 8 F elements) from memory.
        let output = memory_manager.memory.get_extension(addr_output)?;

        // Witness Construction
        //
        // Get the F coefficients from the first two EF elements (value_a).
        let input_part1: Vec<F> = value_a
            .iter()
            .flat_map(BasedVectorSpace::as_basis_coefficients_slice)
            .copied()
            .collect();
        // Get the F coefficients from the third EF element (value_b).
        let input_part2: Vec<F> = value_b.as_basis_coefficients_slice().to_vec();
        // Concatenate the parts to form the full 24-element input for the witness.
        let full_input = [input_part1, input_part2].concat().try_into().unwrap();

        // Construct and return the final witness struct.
        Ok(WitnessPoseidon24 {
            cycle: Some(cycle),
            addr_input_a,
            addr_input_b,
            addr_output,
            input: full_input,
            output: output.as_basis_coefficients_slice().try_into().unwrap(),
        })
    }
}
