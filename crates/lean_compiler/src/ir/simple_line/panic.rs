//! Panic instruction implementation.

use crate::ir::{
    IntermediateInstruction,
    compile::{Compile, CompileContext, CompileResult},
};
use std::fmt::{Display, Formatter};

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

impl crate::ir::simple_line::IndentedDisplay for Panic {}
