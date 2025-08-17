use p3_field::{BasedVectorSpace, dot_product};

use crate::{
    bytecode::operand::{MemOrConstant, MemOrFp},
    constant::{EF, F},
    context::run_context::RunContext,
    errors::vm::VirtualMachineError,
    memory::{address::MemoryAddress, manager::MemoryManager},
    witness::dot_product::WitnessDotProduct,
};

/// An instruction to compute the dot product of two vectors of extension field elements.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DotProductInstruction {
    /// The first operand, a pointer to the start of the first vector.
    pub arg0: MemOrConstant,
    /// The second operand, a pointer to the start of the second vector.
    pub arg1: MemOrConstant,
    /// The destination pointer for the result.
    pub res: MemOrFp,
    /// The number of elements in each vector.
    pub size: usize,
}

impl DotProductInstruction {
    /// Executes the `DotProductExtensionExtension` instruction.
    ///
    /// This function performs the following steps:
    /// 1. Resolves the pointers to the two input vectors and the output location from memory.
    /// 2. Reads the vector data for both operands from memory.
    /// 3. Computes the dot product of the two vectors in the extension field.
    /// 4. Writes the resulting extension field element back to the specified memory location.
    pub fn execute(
        &self,
        run_context: &RunContext,
        memory_manager: &mut MemoryManager,
    ) -> Result<(), VirtualMachineError> {
        // Resolve the memory addresses for the two input vectors and the result.
        let ptr_arg_0: MemoryAddress = run_context
            .value_from_mem_or_constant(&self.arg0, memory_manager)?
            .try_into()?;
        let ptr_arg_1: MemoryAddress = run_context
            .value_from_mem_or_constant(&self.arg1, memory_manager)?
            .try_into()?;
        let ptr_res: MemoryAddress = run_context
            .value_from_mem_or_fp(&self.res, memory_manager)?
            .try_into()?;

        // Read the first vector slice from memory.
        let slice_0 = memory_manager
            .memory
            .get_vectorized_slice_extension(ptr_arg_0, self.size)?;

        // Read the second vector slice from memory.
        let slice_1 = memory_manager
            .memory
            .get_vectorized_slice_extension(ptr_arg_1, self.size)?;

        // Compute the dot product of the two slices by converting them into iterators.
        let dot_product_res = dot_product::<EF, _, _>(slice_0.into_iter(), slice_1.into_iter());

        // Write the resulting vector back to memory.
        memory_manager.load_data::<F>(ptr_res, dot_product_res.as_basis_coefficients_slice())?;

        Ok(())
    }

    /// Generates the witness for the dot product instruction.
    pub fn generate_witness(
        &self,
        cycle: usize,
        run_context: &RunContext,
        memory_manager: &MemoryManager,
    ) -> Result<WitnessDotProduct, VirtualMachineError> {
        // Resolve pointers for inputs and result.
        let addr_0: MemoryAddress = run_context
            .value_from_mem_or_constant(&self.arg0, memory_manager)?
            .try_into()?;
        let addr_1: MemoryAddress = run_context
            .value_from_mem_or_constant(&self.arg1, memory_manager)?
            .try_into()?;
        let addr_res: MemoryAddress = run_context
            .value_from_mem_or_fp(&self.res, memory_manager)?
            .try_into()?;

        // Read the first vector slice from memory.
        let slice_0 = memory_manager
            .memory
            .get_vectorized_slice_extension(addr_0, self.size)?;

        // Read the second vector slice from memory.
        let slice_1 = memory_manager
            .memory
            .get_vectorized_slice_extension(addr_1, self.size)?;

        // Read the result from memory.
        let res = memory_manager.memory.get_extension(addr_res)?;

        // Construct and return the witness.
        Ok(WitnessDotProduct {
            cycle,
            addr_0,
            addr_1,
            addr_res,
            len: self.size,
            slice_0,
            slice_1,
            res,
        })
    }
}
