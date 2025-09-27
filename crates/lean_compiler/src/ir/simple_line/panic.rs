//! Panic instruction implementation.

use crate::ir::{
    IntermediateInstruction,
    compile::{Compile, CompileContext, CompileResult, FindInternalVars},
};
use std::{
    collections::BTreeSet,
    fmt::{Display, Formatter},
};

/// Unconditional program termination instruction.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Panic;

impl Compile for Panic {
    fn compile(
        &self,
        _ctx: &mut CompileContext<'_>,
        _remaining_lines: &[crate::ir::SimpleLine],
    ) -> CompileResult {
        Ok(vec![IntermediateInstruction::Panic])
    }
}

impl Display for Panic {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "panic")
    }
}

impl FindInternalVars for Panic {
    fn find_internal_vars(&self) -> BTreeSet<crate::lang::Var> {
        BTreeSet::new()
    }
}

impl crate::ir::simple_line::IndentedDisplay for Panic {}
