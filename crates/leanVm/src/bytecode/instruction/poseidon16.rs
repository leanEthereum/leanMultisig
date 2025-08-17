use p3_symmetric::Permutation;

use crate::{
    constant::{DIMENSION, F},
    context::run_context::RunContext,
    errors::vm::VirtualMachineError,
    memory::{address::MemoryAddress, manager::MemoryManager},
    witness::poseidon::WitnessPoseidon16,
};

/// Poseidon2 permutation over 16 field elements (2 inputs, 2 outputs).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Poseidon2_16Instruction {
    /// The starting offset `s` from `fp`. The instruction reads 4 pointers from `m[fp+s]` to `m[fp+s+3]`.
    pub shift: usize,
}

impl Poseidon2_16Instruction {
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
    pub fn execute<Perm>(
        &self,
        run_context: &RunContext,
        memory_manager: &mut MemoryManager,
        perm: &Perm,
    ) -> Result<(), VirtualMachineError>
    where
        Perm: Permutation<[F; 2 * DIMENSION]>,
    {
        // Read Pointers from Memory
        //
        // The instruction specifies 4 consecutive pointers starting at `fp + shift`.
        let base_ptr_addr = (run_context.fp + self.shift)?;
        let ptrs: [MemoryAddress; 4] = memory_manager.memory.get_array_as(base_ptr_addr)?;

        // Convert the `MemoryValue` pointers to `MemoryAddress`.
        let [ptr_arg_0, ptr_arg_1, ptr_res_0, ptr_res_1] = ptrs;

        // Read Input Vectors
        //
        // Read the 8-element vectors from the locations pointed to by `ptr_arg_0` and `ptr_arg_1`.
        let arg0 = memory_manager
            .memory
            .get_array_as::<F, DIMENSION>(ptr_arg_0)?;
        let arg1 = memory_manager
            .memory
            .get_array_as::<F, DIMENSION>(ptr_arg_1)?;

        // Perform Hashing
        //
        // Concatenate the two input vectors into a single 16-element array for the permutation.
        let mut state = [arg0, arg1].concat().try_into().unwrap();

        // Apply the Poseidon2 permutation to the state.
        perm.permute_mut(&mut state);

        // Write Output Vectors
        //
        // Split the permuted state back into two 8-element output vectors.
        let res0: [F; DIMENSION] = state[..DIMENSION].try_into().unwrap();
        let res1: [F; DIMENSION] = state[DIMENSION..].try_into().unwrap();

        // Write the output vectors to the memory locations pointed to by `ptr_res_0` and `ptr_res_1`.
        memory_manager.load_data(ptr_res_0, &res0)?;
        memory_manager.load_data(ptr_res_1, &res1)?;

        Ok(())
    }

    /// Generates the witness for a `Poseidon2_16` instruction execution.
    pub fn generate_witness(
        &self,
        cycle: usize,
        run_context: &RunContext,
        memory_manager: &MemoryManager,
    ) -> Result<WitnessPoseidon16, VirtualMachineError> {
        // Read the four pointers (input_a, input_b, output_a, output_b) from memory.
        let base_ptr_addr = (run_context.fp + self.shift)?;
        let [addr_input_a, addr_input_b, addr_output_a, addr_output_b]: [MemoryAddress; 4] =
            memory_manager.memory.get_array_as(base_ptr_addr)?;

        // Read the two 8-element input vectors from their respective addresses.
        let value_a = memory_manager
            .memory
            .get_array_as::<F, DIMENSION>(addr_input_a)?;
        let value_b = memory_manager
            .memory
            .get_array_as::<F, DIMENSION>(addr_input_b)?;

        // Read the two 8-element output vectors.
        let output_a = memory_manager
            .memory
            .get_array_as::<F, DIMENSION>(addr_output_a)?;
        let output_b = memory_manager
            .memory
            .get_array_as::<F, DIMENSION>(addr_output_b)?;

        // Construct and return the witness struct.
        Ok(WitnessPoseidon16 {
            cycle: Some(cycle),
            addr_input_a,
            addr_input_b,
            // The output address is the start of the first output vector.
            addr_output: addr_output_a,
            input: [value_a, value_b].concat().try_into().unwrap(),
            output: [output_a, output_b].concat().try_into().unwrap(),
        })
    }
}
