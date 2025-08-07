use crate::{
    bytecode::{
        operand::{MemOrConstant, MemOrFp},
        operation::Operation,
    },
    context::run_context::RunContext,
    errors::{math::MathError, vm::VirtualMachineError},
    memory::{manager::MemoryManager, val::MemoryValue},
};

/// Performs a basic arithmetic computation: `res = arg_a op arg_b`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ComputationInstruction {
    /// The arithmetic operation to perform (`Add` or `Mul`).
    pub operation: Operation,
    /// The first operand of the computation.
    pub arg_a: MemOrConstant,
    /// The second operand of the computation.
    pub arg_b: MemOrFp,
    /// The memory location or constant that the result must be equal to.
    pub res: MemOrConstant,
}

impl ComputationInstruction {
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
    pub fn execute(
        &self,
        run_context: &RunContext,
        memory_manager: &mut MemoryManager,
    ) -> Result<(), VirtualMachineError> {
        let val_a = run_context.value_from_mem_or_constant(&self.arg_a, memory_manager);
        let val_b = run_context.value_from_mem_or_fp(&self.arg_b, memory_manager);
        let val_res = run_context.value_from_mem_or_constant(&self.res, memory_manager);

        match (val_a, val_b, val_res) {
            // Case 1: a OP b = c — compute c
            (Ok(MemoryValue::Int(a)), Ok(MemoryValue::Int(b)), Ok(MemoryValue::Address(addr))) => {
                let c = self.operation.compute(a, b);
                memory_manager.memory.insert(addr, c)?;
            }
            // Case 2: a OP b = c — recover b
            (Ok(MemoryValue::Int(a)), Ok(MemoryValue::Address(addr)), Ok(MemoryValue::Int(c))) => {
                let b = self
                    .operation
                    .inverse_compute(c, a)
                    .ok_or(MathError::DivisionByZero)?;
                memory_manager.memory.insert(addr, b)?;
            }
            // Case 3: a OP b = c — recover a
            (Ok(MemoryValue::Address(addr)), Ok(MemoryValue::Int(b)), Ok(MemoryValue::Int(c))) => {
                let a = self
                    .operation
                    .inverse_compute(c, b)
                    .ok_or(MathError::DivisionByZero)?;
                memory_manager.memory.insert(addr, a)?;
            }
            // Case 4: a OP b = c — assert equality
            (Ok(MemoryValue::Int(a)), Ok(MemoryValue::Int(b)), Ok(MemoryValue::Int(c))) => {
                let computed = self.operation.compute(a, b);
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
}
