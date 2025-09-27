//! Function return instruction implementation.

use crate::{
    ir::{
        IntermediateInstruction, IntermediateValue,
        compile::{Compile, CompileContext, CompileResult, FindInternalVars},
    },
    lang::SimpleExpr,
};
use lean_vm::Label;
use std::{
    collections::BTreeSet,
    fmt::{Display, Formatter},
};

/// Function return with values.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Return {
    /// Values to return from the function
    pub return_data: Vec<SimpleExpr>,
}

impl Compile for Return {
    fn compile(
        &self,
        ctx: &mut CompileContext<'_>,
        _remaining_lines: &[crate::ir::SimpleLine],
    ) -> CompileResult {
        let mut instructions = Vec::new();

        if ctx.compiler.func_name == "main" {
            // Handle main function return differently - terminate program
            let zero_value_offset = IntermediateValue::MemoryAfterFp {
                offset: ctx.compiler.stack_size.into(),
            };
            ctx.compiler.stack_size += 1;

            instructions.push(IntermediateInstruction::Computation {
                operation: lean_vm::Operation::Add,
                arg_a: IntermediateValue::Constant(0.into()),
                arg_c: IntermediateValue::Constant(0.into()),
                res: zero_value_offset.clone(),
            });

            instructions.push(IntermediateInstruction::Jump {
                dest: IntermediateValue::label(Label::EndProgram),
                updated_fp: Some(zero_value_offset),
            });
        } else {
            for (i, ret_var) in self.return_data.iter().enumerate() {
                instructions.push(IntermediateInstruction::equality(
                    IntermediateValue::MemoryAfterFp {
                        offset: (2 + ctx.compiler.args_count + i).into(),
                    },
                    IntermediateValue::from_simple_expr(ret_var, ctx.compiler),
                ));
            }
            instructions.push(IntermediateInstruction::Jump {
                dest: IntermediateValue::MemoryAfterFp { offset: 0.into() },
                updated_fp: Some(IntermediateValue::MemoryAfterFp { offset: 1.into() }),
            });
        }

        Ok(instructions)
    }
}

impl Display for Return {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let return_data_str = self
            .return_data
            .iter()
            .map(|arg| format!("{}", arg))
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "return {}", return_data_str)
    }
}

impl FindInternalVars for Return {
    fn find_internal_vars(&self) -> BTreeSet<crate::lang::Var> {
        BTreeSet::new()
    }
}

impl crate::ir::simple_line::IndentedDisplay for Return {}
