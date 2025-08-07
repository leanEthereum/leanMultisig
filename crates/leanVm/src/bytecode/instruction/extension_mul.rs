use p3_field::BasedVectorSpace;

use crate::{
    constant::{DIMENSION, EF, F},
    context::run_context::RunContext,
    errors::vm::VirtualMachineError,
    memory::{address::MemoryAddress, manager::MemoryManager},
};

/// Degree-8 extension field multiplication of 2 elements -> 1 result.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExtensionMulInstruction {
    /// An array of three offsets from `fp`. These point to the start of the 8-cell memory blocks
    /// for the two input extension field elements and the resulting output element.
    args: [usize; 3],
}

impl ExtensionMulInstruction {
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
    pub fn execute(
        &self,
        run_context: &RunContext,
        memory_manager: &mut MemoryManager,
    ) -> Result<(), VirtualMachineError> {
        // Get the frame pointer.
        let fp = run_context.fp;

        // Read the memory addresses where the operands and result will reside.
        let ptr_lhs: MemoryAddress = memory_manager.memory.get_as((fp + self.args[0])?)?;
        let ptr_rhs: MemoryAddress = memory_manager.memory.get_as((fp + self.args[1])?)?;
        let ptr_out: MemoryAddress = memory_manager.memory.get_as((fp + self.args[2])?)?;

        // Load the `[F; EF::DIMENSION]` input arrays from memory and convert them into EF elements.
        let lhs = EF::from_basis_coefficients_slice(
            &memory_manager
                .memory
                .get_array_as::<F, DIMENSION>(ptr_lhs)?,
        )
        .unwrap();

        let rhs = EF::from_basis_coefficients_slice(
            &memory_manager
                .memory
                .get_array_as::<F, DIMENSION>(ptr_rhs)?,
        )
        .unwrap();

        // Perform the field multiplication in the extension field.
        let product = lhs * rhs;

        // Write the result converted back into `[F; EF::DIMENSION]` to memory.
        let result_coeffs: &[F] = product.as_basis_coefficients_slice();
        memory_manager.load_data(ptr_out, result_coeffs)?;

        Ok(())
    }
}
