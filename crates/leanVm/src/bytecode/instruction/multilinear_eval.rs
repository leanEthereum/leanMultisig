use p3_field::BasedVectorSpace;
use whir_p3::poly::{coeffs::CoefficientList, multilinear::MultilinearPoint};

use crate::{
    bytecode::operand::{MemOrConstant, MemOrFp},
    constant::{DIMENSION, EF, F},
    context::run_context::RunContext,
    errors::vm::VirtualMachineError,
    memory::{address::MemoryAddress, manager::MemoryManager},
};

/// An instruction to evaluate a multilinear polynomial at a point in the extension field.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MultilinearEvalInstruction {
    /// A pointer to the polynomial's coefficients.
    pub coeffs: MemOrConstant,
    /// A pointer to the evaluation point's coordinates.
    pub point: MemOrConstant,
    /// The destination pointer for the result.
    pub res: MemOrFp,
    /// The number of variables in the multilinear polynomial.
    pub n_vars: usize,
}

impl MultilinearEvalInstruction {
    /// Executes the `MultilinearEval` instruction.
    ///
    /// This function performs the following steps:
    /// 1. Resolves pointers to the polynomial coefficients, evaluation point, and output location.
    /// 2. Reads the polynomial coefficients (base field elements) from memory.
    /// 3. Reads the evaluation point (extension field elements) from memory.
    /// 4. Evaluates the polynomial at the given point.
    /// 5. Writes the resulting extension field element back to memory.
    pub fn execute(
        &self,
        run_context: &RunContext,
        memory_manager: &mut MemoryManager,
    ) -> Result<(), VirtualMachineError> {
        // Resolve the memory addresses for the coefficients, point, and result.
        let ptr_coeffs: MemoryAddress = run_context
            .value_from_mem_or_constant(&self.coeffs, memory_manager)?
            .try_into()?;
        let ptr_point: MemoryAddress = run_context
            .value_from_mem_or_constant(&self.point, memory_manager)?
            .try_into()?;
        let ptr_res: MemoryAddress = run_context
            .value_from_mem_or_fp(&self.res, memory_manager)?
            .try_into()?;

        // Read the polynomial coefficients from memory.
        //
        // The total number of coefficients is 2^n_vars.
        let num_coeffs = 1 << self.n_vars;
        let slice_coeffs: Vec<F> = (0..num_coeffs)
            .map(|i| {
                let addr = (ptr_coeffs + i)?;
                memory_manager.memory.get_as(addr)
            })
            .collect::<Result<_, _>>()?;

        // Read the evaluation point from memory.
        let point: Vec<EF> = (0..self.n_vars)
            .map(|i| {
                let addr = (ptr_point + i)?;
                let vector_coeffs = memory_manager.memory.get_array_as::<F, DIMENSION>(addr)?;
                EF::from_basis_coefficients_slice(&vector_coeffs)
                    .ok_or(VirtualMachineError::InvalidExtensionField)
            })
            .collect::<Result<_, _>>()?;

        // Evaluate the multilinear polynomial.
        let eval = CoefficientList::new(slice_coeffs).evaluate(&MultilinearPoint(point));

        // Write the resulting vector back to memory.
        memory_manager.load_data::<F>(ptr_res, eval.as_basis_coefficients_slice())?;

        Ok(())
    }
}
