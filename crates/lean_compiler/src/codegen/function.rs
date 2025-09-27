use crate::{codegen::*, ir::*, lang::*};
use std::collections::{BTreeMap, BTreeSet};

/// Compiles a single function to intermediate bytecode.
///
/// This function handles the complete compilation of a function body,
/// including variable declaration tracking and instruction generation.
pub fn compile_function(
    function: &SimpleFunction,
    compiler: &mut Compiler,
) -> Result<Vec<IntermediateInstruction>, String> {
    let mut internal_vars = crate::codegen::memory::find_internal_vars(&function.instructions);
    internal_vars.retain(|var| !function.arguments.contains(var));

    // memory layout: pc, fp, args, return_vars, internal_vars
    let mut stack_pos = 2; // Reserve space for pc and fp
    let mut var_positions = BTreeMap::new();

    for (i, var) in function.arguments.iter().enumerate() {
        var_positions.insert(var.clone(), stack_pos + i);
    }
    stack_pos += function.arguments.len();

    stack_pos += function.n_returned_vars;

    for (i, var) in internal_vars.iter().enumerate() {
        var_positions.insert(var.clone(), stack_pos + i);
    }
    stack_pos += internal_vars.len();

    compiler.func_name = function.name.clone();
    compiler.var_positions = var_positions;
    compiler.stack_size = stack_pos;
    compiler.args_count = function.arguments.len();

    let mut declared_vars: BTreeSet<Var> = function.arguments.iter().cloned().collect();
    crate::codegen::instruction::compile_lines(
        &function.instructions,
        compiler,
        None,
        &mut declared_vars,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::SimpleExpr;
    use crate::ir::VarOrConstMallocAccess;

    #[test]
    fn test_compile_simple_function() {
        let function = SimpleFunction {
            name: "add".to_string(),
            arguments: vec!["a".to_string(), "b".to_string()],
            instructions: vec![
                SimpleLine::Assignment {
                    var: VarOrConstMallocAccess::Var("result".to_string()),
                    operation: HighLevelOperation::Add,
                    arg0: SimpleExpr::Var("a".to_string()),
                    arg1: SimpleExpr::Var("b".to_string()),
                },
                SimpleLine::FunctionRet {
                    return_data: vec![SimpleExpr::Var("result".to_string())],
                },
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
}
