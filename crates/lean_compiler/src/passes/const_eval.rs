//! Constant evaluation pass.

use super::{Pass, PassError, PassResult};
use crate::ir::utilities::replace_vars_by_const_in_lines;
use crate::lang::{Function, FunctionCall, Line, Program};
use std::collections::BTreeMap;

/// Pass for handling constant argument evaluation
pub struct ConstEvalPass;

impl ConstEvalPass {
    pub fn new() -> Self {
        Self
    }

    /// Extract all functions with constant arguments
    fn extract_const_functions(program: &Program) -> BTreeMap<String, Function> {
        program
            .functions
            .iter()
            .filter(|(_, func)| func.has_const_arguments())
            .map(|(name, func)| (name.clone(), func.clone()))
            .collect()
    }

    /// Process functions that call constant argument functions
    fn process_function(
        lines: &mut [Line],
        constant_functions: &BTreeMap<String, Function>,
        new_functions: &mut BTreeMap<String, Function>,
    ) {
        for line in lines {
            match line {
                Line::FunctionCall(FunctionCall {
                    function_name,
                    args,
                    return_data: _,
                }) => {
                    if let Some(func) = constant_functions.get(function_name) {
                        Self::handle_const_function_call(func, function_name, args, new_functions);
                    }
                }
                Line::IfCondition(if_cond) => {
                    Self::process_function(&mut if_cond.then_branch, constant_functions, new_functions);
                    Self::process_function(&mut if_cond.else_branch, constant_functions, new_functions);
                }
                Line::ForLoop(for_loop) => {
                    Self::process_function(&mut for_loop.body, constant_functions, new_functions);
                }
                _ => {}
            }
        }
    }

    /// Handle a call to a function with constant arguments
    fn handle_const_function_call(
        func: &Function,
        function_name: &mut String,
        args: &mut Vec<crate::lang::Expression>,
        new_functions: &mut BTreeMap<String, Function>,
    ) {
        // Evaluate constant arguments
        let mut const_evals = Vec::new();
        for (arg_expr, (arg_var, is_constant)) in args.iter().zip(&func.arguments) {
            if *is_constant {
                let const_eval = arg_expr
                    .naive_eval()
                    .unwrap_or_else(|| panic!("Failed to evaluate constant argument: {arg_expr}"));
                const_evals.push((arg_var.clone(), const_eval));
            }
        }

        // Create specialized function name
        let const_func_name = format!(
            "{}_{}",
            function_name,
            const_evals
                .iter()
                .map(|(arg_var, const_eval)| format!("{arg_var}={const_eval}"))
                .collect::<Vec<_>>()
                .join("_")
        );

        // Update the function call to use the specialized name
        *function_name = const_func_name.clone();

        // Remove constant arguments from the call
        *args = args
            .iter()
            .zip(&func.arguments)
            .filter(|(_, (_, is_constant))| !is_constant)
            .map(|(arg_expr, _)| arg_expr.clone())
            .collect();

        // Create the specialized function if it doesn't exist
        if !new_functions.contains_key(&const_func_name) {
            let mut new_body = func.body.clone();
            replace_vars_by_const_in_lines(&mut new_body, &const_evals.iter().cloned().collect());

            new_functions.insert(
                const_func_name.clone(),
                Function {
                    name: const_func_name,
                    arguments: func
                        .arguments
                        .iter()
                        .filter(|(_, is_const)| !is_const)
                        .cloned()
                        .collect(),
                    inlined: false,
                    body: new_body,
                    n_returned_vars: func.n_returned_vars,
                },
            );
        }
    }
}

impl Default for ConstEvalPass {
    fn default() -> Self {
        Self::new()
    }
}

impl Pass for ConstEvalPass {
    fn name(&self) -> &'static str {
        "const_eval"
    }

    fn run(&mut self, program: &mut Program) -> PassResult {
        let mut new_functions = BTreeMap::<String, Function>::new();
        let constant_functions = Self::extract_const_functions(program);

        // First pass: process non-const functions that call const functions
        for func in program.functions.values_mut() {
            if !func.has_const_arguments() {
                Self::process_function(&mut func.body, &constant_functions, &mut new_functions);
            }
        }

        // Process newly created const functions recursively until no more changes
        let mut changed = true;
        let mut const_depth = 0;
        while changed {
            changed = false;
            const_depth += 1;

            if const_depth >= 100 {
                return Err(PassError::Timeout(
                    "Too many levels of constant arguments".to_string(),
                ));
            }

            let mut additional_functions = BTreeMap::new();
            let function_names: Vec<String> = new_functions.keys().cloned().collect();

            for name in function_names {
                if let Some(func) = new_functions.get_mut(&name) {
                    let initial_count = additional_functions.len();
                    Self::process_function(
                        &mut func.body,
                        &constant_functions,
                        &mut additional_functions,
                    );
                    if additional_functions.len() > initial_count {
                        changed = true;
                    }
                }
            }

            // Add newly discovered functions
            for (name, func) in additional_functions {
                if let std::collections::btree_map::Entry::Vacant(e) = new_functions.entry(name) {
                    e.insert(func);
                    changed = true;
                }
            }
        }

        // Add new functions to program and remove old constant functions
        for (name, func) in new_functions {
            program.functions.insert(name, func);
        }

        for const_func in constant_functions.keys() {
            program.functions.remove(const_func);
        }

        Ok(())
    }

    fn requires(&self) -> &[&'static str] {
        &["inline"] // Should run after inlining
    }

    fn invalidates(&self) -> &[&'static str] {
        &[] // Doesn't invalidate other analyses
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::HighLevelOperation;
    use crate::lang::{Assignment, ConstExpression, Expression, FunctionCall, Line, SimpleExpr};
    use std::collections::BTreeMap;

    fn create_const_function(name: &str) -> Function {
        Function {
            name: name.to_string(),
            arguments: vec![("x".to_string(), false), ("size".to_string(), true)],
            inlined: false,
            body: vec![Line::Assignment(Assignment {
                var: "result".to_string(),
                value: Expression::Binary {
                    left: Box::new(Expression::Value(SimpleExpr::Var("x".to_string()))),
                    operation: HighLevelOperation::Add,
                    right: Box::new(Expression::Value(SimpleExpr::Var("size".to_string()))),
                },
            })],
            n_returned_vars: 1,
        }
    }

    #[test]
    fn test_const_eval_pass_simple() {
        let mut program = Program {
            functions: BTreeMap::new(),
        };

        // Create a function with constant arguments
        let const_func = create_const_function("const_func");
        program
            .functions
            .insert("const_func".to_string(), const_func);

        // Create a function that calls const_func with constant value
        let caller_func = Function {
            name: "caller".to_string(),
            arguments: vec![("input".to_string(), false)],
            inlined: false,
            body: vec![Line::FunctionCall(FunctionCall {
                function_name: "const_func".to_string(),
                args: vec![
                    Expression::Value(SimpleExpr::Var("input".to_string())),
                    Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(10))),
                ],
                return_data: vec!["result".to_string()],
            })],
            n_returned_vars: 1,
        };
        program.functions.insert("caller".to_string(), caller_func);

        let mut pass = ConstEvalPass::new();
        let result = pass.run(&mut program);

        assert!(result.is_ok());

        // Original const function should be removed
        assert!(!program.functions.contains_key("const_func"));

        // Should have a specialized function
        let specialized_name = "const_func_size=10";
        assert!(program.functions.contains_key(specialized_name));

        // Caller should call the specialized function
        let caller = program.functions.get("caller").unwrap();
        if let Line::FunctionCall(FunctionCall {
            function_name,
            args,
            ..
        }) = &caller.body[0]
        {
            assert_eq!(function_name, specialized_name);
            assert_eq!(args.len(), 1); // Only non-const arguments
        }
    }

    #[test]
    fn test_const_eval_pass_multiple_values() {
        let mut program = Program {
            functions: BTreeMap::new(),
        };

        let const_func = create_const_function("const_func");
        program
            .functions
            .insert("const_func".to_string(), const_func);

        // Create two callers with different constant values
        let caller1 = Function {
            name: "caller1".to_string(),
            arguments: vec![("input".to_string(), false)],
            inlined: false,
            body: vec![Line::FunctionCall(FunctionCall {
                function_name: "const_func".to_string(),
                args: vec![
                    Expression::Value(SimpleExpr::Var("input".to_string())),
                    Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(5))),
                ],
                return_data: vec!["result1".to_string()],
            })],
            n_returned_vars: 1,
        };
        program.functions.insert("caller1".to_string(), caller1);

        let caller2 = Function {
            name: "caller2".to_string(),
            arguments: vec![("input".to_string(), false)],
            inlined: false,
            body: vec![Line::FunctionCall(FunctionCall {
                function_name: "const_func".to_string(),
                args: vec![
                    Expression::Value(SimpleExpr::Var("input".to_string())),
                    Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(10))),
                ],
                return_data: vec!["result2".to_string()],
            })],
            n_returned_vars: 1,
        };
        program.functions.insert("caller2".to_string(), caller2);

        let mut pass = ConstEvalPass::new();
        let result = pass.run(&mut program);

        assert!(result.is_ok());

        // Should have two specialized functions
        assert!(program.functions.contains_key("const_func_size=5"));
        assert!(program.functions.contains_key("const_func_size=10"));
        assert!(!program.functions.contains_key("const_func"));
    }
}
