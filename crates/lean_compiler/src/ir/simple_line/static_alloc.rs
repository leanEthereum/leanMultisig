//! Static memory allocation instruction implementation.

use crate::{
    ir::compile::{Compile, CompileContext, CompileResult, handle_const_malloc},
    lang::{ConstExpression, ConstMallocLabel, Var},
};
use std::fmt::{Display, Formatter};
use utils::ToUsize;

/// Static compile-time memory allocation.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StaticAlloc {
    /// Variable to store the allocated memory pointer
    pub var: Var,
    /// Size of memory to allocate (known at compile time)
    pub size: ConstExpression,
    /// Label for identifying this allocation
    pub label: ConstMallocLabel,
}

impl Compile for StaticAlloc {
    fn compile(
        &self,
        ctx: &mut CompileContext<'_>,
        _remaining_lines: &[crate::ir::SimpleLine],
    ) -> CompileResult {
        let mut instructions = Vec::new();

        // Evaluate size at compile time
        let size = self.size.naive_eval().unwrap().to_usize();

        // Allocate memory
        handle_const_malloc(
            ctx.declared_vars,
            &mut instructions,
            ctx.compiler,
            &self.var,
            size,
            &self.label,
        );

        Ok(instructions)
    }
}

impl Display for StaticAlloc {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} = malloc({})", self.var, self.size)
    }
}

impl crate::ir::simple_line::IndentedDisplay for StaticAlloc {}
