use p3_field::BasedVectorSpace;
use p3_symmetric::Permutation;

use crate::{
    bytecode::operand::{MemOrConstant, MemOrFp},
    constant::{DIMENSION, F},
    context::run_context::RunContext,
    errors::vm::VirtualMachineError,
    memory::{address::MemoryAddress, manager::MemoryManager},
    witness::poseidon::WitnessPoseidon16,
};

/// Poseidon2 permutation over 16 field elements (2 inputs, 2 outputs).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Poseidon2_16Instruction {
    /// A pointer to the first 8-element input vector.
    pub arg_a: MemOrConstant,
    /// A pointer to the second 8-element input vector.
    pub arg_b: MemOrConstant,
    /// A pointer to the location for the two 8-element output vectors.
    pub res: MemOrFp,
}

impl Poseidon2_16Instruction {
    /// Executes the `Poseidon2_16` precompile instruction.
    ///
    /// This function resolves pointers from its operands to find the memory locations for
    /// two 8-element input vectors and two 8-element output vectors. It reads the inputs,
    /// concatenates them, applies the permutation, and writes the two resulting vectors
    /// back to their designated output locations.
    pub fn execute<Perm>(
        &self,
        run_context: &RunContext,
        memory_manager: &mut MemoryManager,
        perm: &Perm,
    ) -> Result<(), VirtualMachineError>
    where
        Perm: Permutation<[F; 2 * DIMENSION]>,
    {
        // Pointer Resolution
        //
        // Resolve the pointer to the first input vector from the `arg_a` operand.
        let ptr_arg_a: MemoryAddress = run_context
            .value_from_mem_or_constant(&self.arg_a, memory_manager)?
            .try_into()?;
        // Resolve the pointer to the second input vector from the `arg_b` operand.
        let ptr_arg_b: MemoryAddress = run_context
            .value_from_mem_or_constant(&self.arg_b, memory_manager)?
            .try_into()?;
        // Resolve the pointer for the start of the output block from the `res` operand.
        let ptr_res: MemoryAddress = run_context
            .value_from_mem_or_fp(&self.res, memory_manager)?
            .try_into()?;
        // The second output vector will be stored immediately after the first one.
        let ptr_res_b = (ptr_res + 1)?;

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

        // Hashing
        //
        // Concatenate the two input vectors into a single 16-element array for the permutation.
        let mut state = [arg0, arg1].concat().try_into().unwrap();
        // Apply the Poseidon2 permutation to the state.
        perm.permute_mut(&mut state);

        // Data Writing
        //
        // Split the permuted state back into two 8-element output vectors.
        let res0: [F; DIMENSION] = state[..DIMENSION].try_into().unwrap();
        let res1: [F; DIMENSION] = state[DIMENSION..].try_into().unwrap();
        // Write the first output vector to its memory location.
        memory_manager.load_data(ptr_res, &res0)?;
        // Write the second output vector to its memory location.
        memory_manager.load_data(ptr_res_b, &res1)?;

        Ok(())
    }

    /// Generates the witness for a `Poseidon2_16` instruction execution.
    pub fn generate_witness(
        &self,
        cycle: usize,
        run_context: &RunContext,
        memory_manager: &MemoryManager,
    ) -> Result<WitnessPoseidon16, VirtualMachineError> {
        // Pointer Resolution
        //
        // Resolve the pointer to the first input vector from the `arg_a` operand.
        let addr_input_a: MemoryAddress = run_context
            .value_from_mem_or_constant(&self.arg_a, memory_manager)?
            .try_into()?;
        // Resolve the pointer to the second input vector from the `arg_b` operand.
        let addr_input_b: MemoryAddress = run_context
            .value_from_mem_or_constant(&self.arg_b, memory_manager)?
            .try_into()?;
        // Resolve the pointer for the start of the output block from the `res` operand.
        let addr_output: MemoryAddress = run_context
            .value_from_mem_or_fp(&self.res, memory_manager)?
            .try_into()?;

        // Data Reading
        //
        // Read the first 8-element input vector from its respective address.
        let value_a = memory_manager
            .memory
            .get_array_as::<F, DIMENSION>(addr_input_a)?;
        // Read the second 8-element input vector from its respective address.
        let value_b = memory_manager
            .memory
            .get_array_as::<F, DIMENSION>(addr_input_b)?;
        // Read the full 16-element output from memory, starting at the output address.
        let output = memory_manager
            .memory
            .get_vectorized_slice_extension(addr_output, 2)?;
        let output_coeffs: Vec<F> = output
            .iter()
            .flat_map(BasedVectorSpace::as_basis_coefficients_slice)
            .copied()
            .collect();

        // Witness Construction
        //
        // Construct and return the witness struct.
        Ok(WitnessPoseidon16 {
            cycle: Some(cycle),
            addr_input_a,
            addr_input_b,
            addr_output,
            input: [value_a, value_b].concat().try_into().unwrap(),
            output: output_coeffs.try_into().unwrap(),
        })
    }
}
