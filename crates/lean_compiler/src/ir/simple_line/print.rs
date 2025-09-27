//! Print instruction implementation.

use crate::{
    ir::{
        IntermediateInstruction, IntermediateValue,
        compile::{Compile, CompileContext, CompileResult},
    },
    lang::SimpleExpr,
};
use std::fmt::{Display, Formatter};

/// Debug print statement.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Print {
    /// Line information for debugging context
    pub line_info: String,
    /// Expressions to print
    pub content: Vec<SimpleExpr>,
}

impl Compile for Print {
    fn compile(
        &self,
        ctx: &mut CompileContext<'_>,
        _remaining_lines: &[crate::ir::SimpleLine],
    ) -> CompileResult {
        let instruction = IntermediateInstruction::Print {
            line_info: self.line_info.clone(),
            content: self
                .content
                .iter()
                .map(|c| IntermediateValue::from_simple_expr(c, ctx.compiler))
                .collect(),
        };

        Ok(vec![instruction])
    }
}

impl Display for Print {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let content_str = self.content
            .iter()
            .map(|c| format!("{}", c))
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "print({})", content_str)
    }
}

impl crate::ir::simple_line::IndentedDisplay for Print {}
