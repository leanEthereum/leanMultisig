use p3_symmetric::Permutation;

use crate::{
    constant::{DIMENSION, F},
    context::run_context::RunContext,
    errors::vm::VirtualMachineError,
    memory::{address::MemoryAddress, manager::MemoryManager},
};

/// Poseidon2 permutation over 24 field elements (3 inputs, 3 outputs).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Poseidon2_24Instruction {
    /// The starting offset from `fp`. The instruction reads 6 pointers from `m[fp+shift]` to `m[fp+shift+5]`.
    pub shift: usize,
}

impl Poseidon2_24Instruction {
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
    pub fn execute<Perm>(
        &self,
        run_context: &RunContext,
        memory_manager: &mut MemoryManager,
        perm: &Perm,
    ) -> Result<(), VirtualMachineError>
    where
        Perm: Permutation<[F; 3 * DIMENSION]>,
    {
        // Read Pointers from Memory
        //
        // The instruction specifies 6 consecutive pointers starting at `fp + shift`.
        let ptr_addr = (run_context.fp + self.shift)?;
        let ptrs: [MemoryAddress; 6] = memory_manager.memory.get_array_as(ptr_addr)?;

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
        let arg0 = memory_manager
            .memory
            .get_array_as::<F, DIMENSION>(ptr_arg_0)?;
        let arg1 = memory_manager
            .memory
            .get_array_as::<F, DIMENSION>(ptr_arg_1)?;
        let arg2 = memory_manager
            .memory
            .get_array_as::<F, DIMENSION>(ptr_arg_2)?;

        // Perform Hashing
        //
        // Concatenate the three input vectors into a single 24-element array for the permutation.
        let mut state = [arg0, arg1, arg2].concat().try_into().unwrap();

        // Apply the Poseidon2 permutation to the state.
        perm.permute_mut(&mut state);

        // Write Output Vectors
        //
        // Split the permuted state back into three 8-element output vectors.
        let res0: [F; DIMENSION] = state[..DIMENSION].try_into().unwrap();
        let res1: [F; DIMENSION] = state[DIMENSION..2 * DIMENSION].try_into().unwrap();
        let res2: [F; DIMENSION] = state[2 * DIMENSION..].try_into().unwrap();

        // Write the output vectors to the memory locations pointed to by the result pointers.
        memory_manager.load_data(ptr_res_0, &res0)?;
        memory_manager.load_data(ptr_res_1, &res1)?;
        memory_manager.load_data(ptr_res_2, &res2)?;

        Ok(())
    }
}
