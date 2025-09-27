//! Simple function representation and compilation.

use crate::{
    ir::{
        IntermediateInstruction,
        compiler::{Compile, CompileContext, CompileResult, Compiler},
        simple_line::{SimpleLine, compile_lines, find_internal_vars},
    },
    lang::Var,
};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{Display, Formatter};

/// Simplified function representation.
#[derive(Debug, Clone)]
pub struct SimpleFunction {
    pub name: String,
    pub arguments: Vec<Var>,
    pub n_returned_vars: usize,
    pub instructions: Vec<SimpleLine>,
}

impl Display for SimpleFunction {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let args_str = self.arguments.join(", ");
        let instructions_str = self
            .instructions
            .iter()
            .map(|inst| format!("    {}", inst))
            .collect::<Vec<_>>()
            .join("\n");

        write!(
            f,
            "fn {}({}) -> {} {{\n{}\n}}",
            self.name, args_str, self.n_returned_vars, instructions_str
        )
    }
}

impl Compile for SimpleFunction {
    fn compile(
        &self,
        ctx: &mut CompileContext<'_>,
        _remaining_lines: &[SimpleLine],
    ) -> CompileResult {
        let mut internal_vars = find_internal_vars(&self.instructions);
        internal_vars.retain(|var| !self.arguments.contains(var));

        // memory layout: pc, fp, args, return_vars, internal_vars
        let mut stack_pos = 2; // Reserve space for pc and fp
        let mut var_positions = BTreeMap::new();

        for (i, var) in self.arguments.iter().enumerate() {
            var_positions.insert(var.clone(), stack_pos + i);
        }
        stack_pos += self.arguments.len();

        stack_pos += self.n_returned_vars;

        for (i, var) in internal_vars.iter().enumerate() {
            var_positions.insert(var.clone(), stack_pos + i);
        }
        stack_pos += internal_vars.len();

        ctx.compiler.func_name = self.name.clone();
        ctx.compiler.var_positions = var_positions;
        ctx.compiler.stack_size = stack_pos;
        ctx.compiler.args_count = self.arguments.len();

        let mut declared_vars: BTreeSet<Var> = self.arguments.iter().cloned().collect();
        compile_lines(&self.instructions, ctx.compiler, None, &mut declared_vars)
    }
}

/// Compiles a single function to intermediate bytecode.
pub fn compile_function(
    function: &SimpleFunction,
    compiler: &mut Compiler,
) -> Result<Vec<IntermediateInstruction>, String> {
    use std::collections::BTreeSet;
    let mut declared_vars = BTreeSet::new();
    let mut ctx = CompileContext::new(compiler, None, &mut declared_vars);
    function.compile(&mut ctx, &[])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{
        HighLevelOperation, VarOrConstMallocAccess,
        simple_line::{Assignment, Return},
    };
    use crate::lang::SimpleExpr;

    #[test]
    fn test_compile_simple_function() {
        let function = SimpleFunction {
            name: "add".to_string(),
            arguments: vec!["a".to_string(), "b".to_string()],
            instructions: vec![
                SimpleLine::Assignment(Assignment {
                    var: VarOrConstMallocAccess::Var("result".to_string()),
                    operation: HighLevelOperation::Add,
                    arg0: SimpleExpr::Var("a".to_string()),
                    arg1: SimpleExpr::Var("b".to_string()),
                }),
                SimpleLine::Return(Return {
                    return_data: vec![SimpleExpr::Var("result".to_string())],
                }),
            ],
            n_returned_vars: 1,
        };

        let mut compiler = Compiler::new();

        let result = compile_function(&function, &mut compiler);
        assert!(result.is_ok());

        let instructions = result.unwrap();
        assert!(!instructions.is_empty());

        // Should contain at least the assignment and return
        assert!(
            instructions
                .iter()
                .any(|inst| matches!(inst, IntermediateInstruction::Computation { .. }))
        );
    }

    #[test]
    fn test_simple_function_display() {
        let function = SimpleFunction {
            name: "test".to_string(),
            arguments: vec!["x".to_string(), "y".to_string()],
            n_returned_vars: 1,
            instructions: vec![SimpleLine::Assignment(Assignment {
                var: VarOrConstMallocAccess::Var("result".to_string()),
                operation: HighLevelOperation::Add,
                arg0: SimpleExpr::Var("x".to_string()),
                arg1: SimpleExpr::Var("y".to_string()),
            })],
        };

        let display_str = format!("{}", function);
        assert!(display_str.contains("fn test(x, y) -> 1"));
        assert!(display_str.contains("result = x + y"));
    }
}
