//! Compilation context for sharing state across instruction compilers.

use crate::{ir::compiler::state::Compiler, lang::Var};
use lean_vm::Label;
use std::collections::BTreeSet;

/// Compilation context shared across instruction compilers.
#[derive(Debug)]
pub struct CompileContext<'a> {
    /// The main compiler instance with bytecode generation state
    pub compiler: &'a mut Compiler,
    /// Optional jump target for control flow continuation
    pub final_jump: Option<Label>,
    /// Set of variables declared in current scope
    pub declared_vars: &'a mut BTreeSet<Var>,
}

impl<'a> CompileContext<'a> {
    /// Creates a new compilation context.
    pub const fn new(
        compiler: &'a mut Compiler,
        final_jump: Option<Label>,
        declared_vars: &'a mut BTreeSet<Var>,
    ) -> Self {
        Self {
            compiler,
            final_jump,
            declared_vars,
        }
    }
}
