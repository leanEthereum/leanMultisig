use p3_field::{BasedVectorSpace, dot_product};

use crate::{
    bytecode::operand::{MemOrConstant, MemOrFp},
    constant::{DIMENSION, EF, F},
    context::run_context::RunContext,
    errors::vm::VirtualMachineError,
    memory::{address::MemoryAddress, manager::MemoryManager},
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
        let slice_0: Vec<EF> = (0..self.size)
            .map(|i| {
                let addr = (ptr_arg_0 + i)?;
                let vector_coeffs = memory_manager.memory.get_array_as::<F, DIMENSION>(addr)?;
                EF::from_basis_coefficients_slice(&vector_coeffs)
                    .ok_or(VirtualMachineError::InvalidExtensionField)
            })
            .collect::<Result<_, _>>()?;

        // Read the second vector slice from memory.
        let slice_1: Vec<EF> = (0..self.size)
            .map(|i| {
                let addr = (ptr_arg_1 + i)?;
                let vector_coeffs = memory_manager.memory.get_array_as::<F, DIMENSION>(addr)?;
                EF::from_basis_coefficients_slice(&vector_coeffs)
                    .ok_or(VirtualMachineError::InvalidExtensionField)
            })
            .collect::<Result<_, _>>()?;

        // Compute the dot product of the two slices by converting them into iterators.
        let dot_product_res = dot_product::<EF, _, _>(slice_0.into_iter(), slice_1.into_iter());

        // Write the resulting vector back to memory.
        memory_manager.load_data::<F>(ptr_res, dot_product_res.as_basis_coefficients_slice())?;

        Ok(())
    }
}
