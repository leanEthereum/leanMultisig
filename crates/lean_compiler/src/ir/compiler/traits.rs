//! Compilation traits for IR instructions.

use super::{context::CompileContext, types::CompileResult};
use crate::lang::Var;
use std::collections::BTreeSet;

/// Core trait for compiling instruction types into intermediate bytecode.
pub trait Compile {
    /// Compiles the instruction into intermediate bytecode.
    ///
    /// # Arguments
    /// * `ctx` - Compilation context containing compiler state and scope information
    /// * `remaining_lines` - Remaining SimpleLine instructions in the current block for control flow
    ///
    /// # Returns
    /// Vector of intermediate instructions or compilation error
    fn compile(
        &self,
        ctx: &mut CompileContext<'_>,
        remaining_lines: &[crate::ir::SimpleLine],
    ) -> CompileResult;
}

/// Trait for finding internal variables declared by instructions.
pub trait FindInternalVars {
    /// Finds all internal variables declared within this instruction.
    ///
    /// # Returns
    /// Set of variable names that need stack allocation
    fn find_internal_vars(&self) -> BTreeSet<Var>;
}
