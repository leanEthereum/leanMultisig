//! Dynamic memory allocation instruction implementation.

use crate::{
    ir::{
        IntermediateInstruction, IntermediateValue,
        compile::{Compile, CompileContext, CompileResult},
    },
    lang::{SimpleExpr, Var},
};
use std::fmt::{Display, Formatter};

/// Dynamic memory allocation.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DynamicAlloc {
    /// Variable to store the allocated memory pointer
    pub var: Var,
    /// Size of memory to allocate
    pub size: SimpleExpr,
    /// Whether allocation should be vectorized
    pub vectorized: bool,
    /// Length of vectorization if vectorized
    pub vectorized_len: SimpleExpr,
}

impl Compile for DynamicAlloc {
    fn compile(
        &self,
        ctx: &mut CompileContext<'_>,
        _remaining_lines: &[crate::ir::SimpleLine],
    ) -> CompileResult {
        ctx.declared_vars.insert(self.var.clone());

        let instruction = IntermediateInstruction::RequestMemory {
            offset: ctx.compiler.get_offset(&self.var.clone().into()),
            size: IntermediateValue::from_simple_expr(&self.size, ctx.compiler),
            vectorized: self.vectorized,
            vectorized_len: IntermediateValue::from_simple_expr(&self.vectorized_len, ctx.compiler),
        };

        Ok(vec![instruction])
    }
}

impl Display for DynamicAlloc {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.vectorized {
            write!(f, "{} = malloc_vec({}, {})", self.var, self.size, self.vectorized_len)
        } else {
            write!(f, "{} = malloc({})", self.var, self.size)
        }
    }
}

impl crate::ir::simple_line::IndentedDisplay for DynamicAlloc {}
