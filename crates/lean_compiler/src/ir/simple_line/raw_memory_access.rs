//! Raw memory access instruction implementation.

use crate::{
    ir::{
        IntermediateInstruction,
        compile::{Compile, CompileContext, CompileResult, validate_vars_declared},
    },
    lang::{ConstExpression, SimpleExpr},
};
use std::fmt::{Display, Formatter};

/// Direct memory access operations.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RawMemoryAccess {
    /// Result variable to store the read value
    pub res: SimpleExpr,
    /// Base memory index expression
    pub index: SimpleExpr,
    /// Constant offset to add to index
    pub shift: ConstExpression,
}

impl Compile for RawMemoryAccess {
    fn compile(
        &self,
        ctx: &mut CompileContext<'_>,
        _remaining_lines: &[crate::ir::SimpleLine],
    ) -> CompileResult {
        validate_vars_declared(&[&self.index], ctx.declared_vars)?;

        if let SimpleExpr::Var(var) = &self.res {
            ctx.declared_vars.insert(var.clone());
        }

        let shift_0 = match &self.index {
            SimpleExpr::Constant(c) => c.clone(),
            _ => ctx.compiler.get_offset(&self.index.clone().try_into().unwrap()),
        };

        let instruction = IntermediateInstruction::Deref {
            shift_0,
            shift_1: self.shift.clone(),
            res: self.res.to_mem_after_fp_or_constant(ctx.compiler),
        };

        Ok(vec![instruction])
    }
}

impl Display for RawMemoryAccess {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "memory[{} + {}] = {}", self.index, self.shift, self.res)
    }
}

impl crate::ir::simple_line::IndentedDisplay for RawMemoryAccess {}
