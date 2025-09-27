//! Location report instruction implementation.

use crate::ir::{
    IntermediateInstruction,
    compile::{Compile, CompileContext, CompileResult},
};
use lean_vm::SourceLineNumber;
use std::fmt::{Display, Formatter};

/// Source location tracking for debugging.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LocationReport {
    /// Source line number for location tracking
    pub location: SourceLineNumber,
}

impl Compile for LocationReport {
    fn compile(
        &self,
        _ctx: &mut CompileContext<'_>,
        _remaining_lines: &[crate::ir::SimpleLine],
    ) -> CompileResult {
        let instruction = IntermediateInstruction::LocationReport {
            location: self.location,
        };

        Ok(vec![instruction])
    }
}

impl Display for LocationReport {
    fn fmt(&self, _f: &mut Formatter<'_>) -> std::fmt::Result {
        // Location reports are typically not displayed
        Ok(())
    }
}

impl crate::ir::simple_line::IndentedDisplay for LocationReport {}
