//! Function inlining pass.

use super::{Pass, PassError, PassResult};
use crate::analysis::control_flow::ControlFlowAnalyzer;
use crate::lang::{Expression, Function, Line, Program, SimpleExpr, Var};
use std::collections::BTreeMap;

/// Counter for generating unique variable names during inlining
struct Counter {
    value: usize,
}

impl Counter {
    fn new() -> Self {
        Self { value: 0 }
    }

    fn next_value(&mut self) -> usize {
        let current = self.value;
        self.value += 1;
        current
    }
}

/// Pass for inlining functions marked as `inlined`
pub struct InlinePass {
    max_iterations: usize,
}

impl InlinePass {
    /// Create a new inline pass with default settings
    pub fn new() -> Self {
        Self { max_iterations: 10 }
    }

    /// Create an inline pass with custom maximum iterations
    pub fn with_max_iterations(max_iterations: usize) -> Self {
        Self { max_iterations }
    }

    /// Extract all inlined functions from the program
    fn extract_inlined_functions(program: &Program) -> BTreeMap<String, Function> {
        program
            .functions
            .iter()
            .filter(|(_, func)| func.inlined)
            .map(|(name, func)| (name.clone(), func.clone()))
            .collect()
    }

    /// Process a single function for inline calls
    fn process_function(
        function: &mut Function,
        inlined_functions: &BTreeMap<String, Function>,
    ) -> bool {
        let mut counter1 = Counter::new();
        let mut counter2 = Counter::new();
        let old_body = function.body.clone();

        Self::process_lines(
            &mut function.body,
            inlined_functions,
            &mut counter1,
            &mut counter2,
        );

        function.body != old_body
    }

    /// Process lines recursively for inline calls
    fn process_lines(
        lines: &mut Vec<Line>,
        inlined_functions: &BTreeMap<String, Function>,
        inlined_var_counter: &mut Counter,
        total_inlined_counter: &mut Counter,
    ) {
        for i in (0..lines.len()).rev() {
            match &mut lines[i] {
                Line::FunctionCall(call) => {
                    let function_name = &call.function_name;
                    let args = &call.args;
                    let return_data = &call.return_data;
                    if let Some(func) = inlined_functions.get(function_name) {
                        let inlined_lines = Self::inline_function_call(
                            func,
                            args,
                            return_data,
                            inlined_var_counter,
                            total_inlined_counter,
                        );

                        lines.remove(i); // Remove the function call
                        lines.splice(i..i, inlined_lines); // Insert inlined content
                    }
                }
                Line::IfCondition(if_cond) => {
                    Self::process_lines(
                        &mut if_cond.then_branch,
                        inlined_functions,
                        inlined_var_counter,
                        total_inlined_counter,
                    );
                    Self::process_lines(
                        &mut if_cond.else_branch,
                        inlined_functions,
                        inlined_var_counter,
                        total_inlined_counter,
                    );
                }
                Line::ForLoop(for_loop) => {
                    Self::process_lines(
                        &mut for_loop.body,
                        inlined_functions,
                        inlined_var_counter,
                        total_inlined_counter,
                    );
                }
                Line::Match(match_stmt) => {
                    for (_, arm) in &mut match_stmt.arms {
                        Self::process_lines(
                            arm,
                            inlined_functions,
                            inlined_var_counter,
                            total_inlined_counter,
                        );
                    }
                }
                _ => {}
            }
        }
    }

    /// Inline a single function call
    fn inline_function_call(
        func: &Function,
        args: &[Expression],
        return_data: &[Var],
        inlined_var_counter: &mut Counter,
        total_inlined_counter: &mut Counter,
    ) -> Vec<Line> {
        let mut inlined_lines = vec![];

        // Handle complex arguments by creating auxiliary variables
        let mut simplified_args = vec![];
        for arg in args {
            if let Expression::Value(simple_expr) = arg {
                simplified_args.push(simple_expr.clone());
            } else {
                let aux_var = format!("@inlined_var_{}", inlined_var_counter.next_value());
                inlined_lines.push(Line::Assignment(crate::lang::ast::statement::Assignment {
                    var: aux_var.clone(),
                    value: arg.clone(),
                }));
                simplified_args.push(SimpleExpr::Var(aux_var));
            }
        }

        // Create argument mapping
        assert_eq!(simplified_args.len(), func.arguments.len());
        let inlined_args = func
            .arguments
            .iter()
            .zip(&simplified_args)
            .map(|((var, _), expr)| (var.clone(), expr.clone()))
            .collect::<BTreeMap<_, _>>();

        // Inline the function body
        let mut func_body = func.body.clone();
        Self::inline_lines(
            &mut func_body,
            &inlined_args,
            return_data,
            total_inlined_counter.next_value(),
        );
        inlined_lines.extend(func_body);

        inlined_lines
    }

    /// Inline variables and expressions in function body
    fn inline_lines(
        lines: &mut Vec<Line>,
        args: &BTreeMap<Var, SimpleExpr>,
        res: &[Var],
        inlining_count: usize,
    ) {
        // Check if we need SSA repair for this function body
        let needs_ssa_repair = {
            let analysis = ControlFlowAnalyzer::analyze(lines);
            analysis.needs_ssa_repair()
        };

        let mut lines_to_replace = vec![];
        for (i, line) in lines.iter_mut().enumerate() {
            Self::process_line_for_inlining(
                line,
                args,
                inlining_count,
                res,
                &mut lines_to_replace,
                i,
            );
        }

        // Apply return statement replacements
        for (i, new_lines) in lines_to_replace.into_iter().rev() {
            lines.splice(i..=i, new_lines);
        }

        // Apply SSA repair if needed
        if needs_ssa_repair {
            crate::passes::ssa_repair::repair_ssa_violations(lines, res);
        }
    }

    /// Process a single line for inlining transformations
    fn process_line_for_inlining(
        line: &mut Line,
        args: &BTreeMap<Var, SimpleExpr>,
        inlining_count: usize,
        res: &[Var],
        lines_to_replace: &mut Vec<(usize, Vec<Line>)>,
        line_index: usize,
    ) {
        match line {
            Line::Match(match_stmt) => {
                Self::inline_expr(&mut match_stmt.value, args, inlining_count);
                for (_, statements) in &mut match_stmt.arms {
                    Self::inline_lines(statements, args, res, inlining_count);
                }
            }
            Line::Assignment(assignment) => {
                Self::inline_expr(&mut assignment.value, args, inlining_count);
                Self::inline_internal_var(&mut assignment.var, inlining_count);
            }
            Line::IfCondition(if_cond) => {
                Self::inline_boolean(&mut if_cond.condition, args, inlining_count);
                Self::inline_lines(&mut if_cond.then_branch, args, res, inlining_count);
                Self::inline_lines(&mut if_cond.else_branch, args, res, inlining_count);
            }
            Line::FunctionCall(call) => {
                for arg in &mut call.args {
                    Self::inline_expr(arg, args, inlining_count);
                }
                for return_var in &mut call.return_data {
                    Self::inline_internal_var(return_var, inlining_count);
                }
            }
            Line::Assert(assert) => {
                Self::inline_boolean(&mut assert.condition, args, inlining_count);
            }
            Line::FunctionRet(ret) => {
                let return_data = &mut ret.return_data;
                assert_eq!(return_data.len(), res.len());

                for expr in return_data.iter_mut() {
                    Self::inline_expr(expr, args, inlining_count);
                }

                // Replace return statements with assignments
                let new_lines = res
                    .iter()
                    .zip(return_data)
                    .map(|(res_var, expr)| Line::Assignment(crate::lang::ast::statement::Assignment {
                        var: res_var.clone(),
                        value: expr.clone(),
                    }))
                    .collect::<Vec<_>>();

                lines_to_replace.push((line_index, new_lines));
            }
            Line::MAlloc(malloc) => {
                Self::inline_expr(&mut malloc.size, args, inlining_count);
                Self::inline_expr(&mut malloc.vectorized_len, args, inlining_count);
                Self::inline_internal_var(&mut malloc.var, inlining_count);
            }
            Line::Precompile(precompile) => {
                for arg in &mut precompile.args {
                    Self::inline_expr(arg, args, inlining_count);
                }
            }
            Line::Print(print) => {
                for var in &mut print.content {
                    Self::inline_expr(var, args, inlining_count);
                }
            }
            Line::DecomposeBits(decompose) => {
                for expr in &mut decompose.to_decompose {
                    Self::inline_expr(expr, args, inlining_count);
                }
                Self::inline_internal_var(&mut decompose.var, inlining_count);
            }
            Line::CounterHint(hint) => {
                Self::inline_internal_var(&mut hint.var, inlining_count);
            }
            Line::ForLoop(for_loop) => {
                Self::inline_lines(&mut for_loop.body, args, res, inlining_count);
                Self::inline_internal_var(&mut for_loop.iterator, inlining_count);
                Self::inline_expr(&mut for_loop.start, args, inlining_count);
                Self::inline_expr(&mut for_loop.end, args, inlining_count);
            }
            Line::ArrayAssign(array_assign) => {
                Self::inline_simple_expr(&mut array_assign.array, args, inlining_count);
                Self::inline_expr(&mut array_assign.index, args, inlining_count);
                Self::inline_expr(&mut array_assign.value, args, inlining_count);
            }
            Line::Panic(_) | Line::Break(_) | Line::LocationReport(_) => {}
        }
    }

    /// Inline expressions by replacing variables with their arguments
    fn inline_expr(expr: &mut Expression, args: &BTreeMap<Var, SimpleExpr>, inlining_count: usize) {
        match expr {
            Expression::Value(value) => {
                Self::inline_simple_expr(value, args, inlining_count);
            }
            Expression::ArrayAccess { array, index } => {
                Self::inline_simple_expr(array, args, inlining_count);
                Self::inline_expr(index, args, inlining_count);
            }
            Expression::Binary { left, right, .. } => {
                Self::inline_expr(left, args, inlining_count);
                Self::inline_expr(right, args, inlining_count);
            }
            Expression::Log2Ceil { value } => {
                Self::inline_expr(value, args, inlining_count);
            }
        }
    }

    /// Inline simple expressions (variables and constants)
    fn inline_simple_expr(
        simple_expr: &mut SimpleExpr,
        args: &BTreeMap<Var, SimpleExpr>,
        inlining_count: usize,
    ) {
        if let SimpleExpr::Var(var) = simple_expr {
            if let Some(replacement) = args.get(var) {
                *simple_expr = replacement.clone();
            } else {
                *var = format!("@inlined_var_{inlining_count}_{var}");
            }
        }
    }

    /// Inline boolean conditions
    fn inline_boolean(
        condition: &mut crate::lang::Boolean,
        args: &BTreeMap<Var, SimpleExpr>,
        inlining_count: usize,
    ) {
        match condition {
            crate::lang::Boolean::Equal { left, right }
            | crate::lang::Boolean::Different { left, right } => {
                Self::inline_expr(left, args, inlining_count);
                Self::inline_expr(right, args, inlining_count);
            }
        }
    }

    /// Rename internal variables to avoid conflicts
    fn inline_internal_var(var: &mut Var, inlining_count: usize) {
        // Don't rename return flag variables
        if var.starts_with("@inlined_returned_") {
            return;
        }
        *var = format!("@inlined_var_{inlining_count}_{var}");
    }
}

impl Default for InlinePass {
    fn default() -> Self {
        Self::new()
    }
}

impl Pass for InlinePass {
    fn name(&self) -> &'static str {
        "inline"
    }

    fn run(&mut self, program: &mut Program) -> PassResult {
        let inlined_functions = Self::extract_inlined_functions(program);

        // Check for constant arguments in inlined functions (not supported yet)
        for func in inlined_functions.values() {
            if func.has_const_arguments() {
                return Err(PassError::Failed(
                    "Inlined functions with constant arguments are not supported yet".to_string(),
                ));
            }
        }

        // Process inline functions iteratively to handle dependencies
        let mut iterations = 0;
        while iterations < self.max_iterations {
            let mut any_changes = false;

            // Process non-inlined functions
            for func in program.functions.values_mut() {
                if !func.inlined && Self::process_function(func, &inlined_functions) {
                    any_changes = true;
                }
            }

            // Process inlined functions that may call other inlined functions
            for func in program.functions.values_mut() {
                if func.inlined && Self::process_function(func, &inlined_functions) {
                    any_changes = true;
                }
            }

            if !any_changes {
                break;
            }

            iterations += 1;
        }

        if iterations >= self.max_iterations {
            return Err(PassError::Timeout(
                "Too many iterations processing inline functions".to_string(),
            ));
        }

        // Remove all inlined functions from the program
        for func_name in inlined_functions.keys() {
            program.functions.remove(func_name);
        }

        Ok(())
    }

    fn requires(&self) -> &[&'static str] {
        &[] // No dependencies
    }

    fn invalidates(&self) -> &[&'static str] {
        &["control_flow", "ssa"] // Inlining changes control flow and SSA properties
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::HighLevelOperation;
    use crate::lang::{
        Assignment, Boolean, ConstExpression, FunctionCall, FunctionRet, IfCondition,
    };
    use std::collections::BTreeMap;

    fn create_test_program() -> Program {
        Program {
            functions: BTreeMap::new(),
        }
    }

    fn create_simple_function(name: &str, inlined: bool) -> Function {
        Function {
            name: name.to_string(),
            arguments: vec![("x".to_string(), false), ("y".to_string(), false)],
            inlined,
            body: vec![Line::Assignment(Assignment {
                var: "result".to_string(),
                value: Expression::Binary {
                    left: Box::new(Expression::Value(SimpleExpr::Var("x".to_string()))),
                    operation: HighLevelOperation::Add,
                    right: Box::new(Expression::Value(SimpleExpr::Var("y".to_string()))),
                },
            })],
            n_returned_vars: 1,
        }
    }

    #[test]
    fn test_inline_pass_simple() {
        let mut program = create_test_program();

        // Create an inlined function
        let inlined_func = create_simple_function("inline_add", true);
        program
            .functions
            .insert("inline_add".to_string(), inlined_func);

        // Create a function that calls the inlined function
        let caller_func = Function {
            name: "caller".to_string(),
            arguments: vec![("a".to_string(), false), ("b".to_string(), false)],
            inlined: false,
            body: vec![Line::FunctionCall(FunctionCall {
                function_name: "inline_add".to_string(),
                args: vec![
                    Expression::Value(SimpleExpr::Var("a".to_string())),
                    Expression::Value(SimpleExpr::Var("b".to_string())),
                ],
                return_data: vec!["sum".to_string()],
            })],
            n_returned_vars: 1,
        };
        program.functions.insert("caller".to_string(), caller_func);

        let mut pass = InlinePass::new();
        let result = pass.run(&mut program);

        assert!(result.is_ok());
        assert!(!program.functions.contains_key("inline_add")); // Inlined function removed

        // Check that caller was modified
        let caller = program.functions.get("caller").unwrap();
        assert_eq!(caller.body.len(), 1);
    }

    #[test]
    fn test_inline_pass_with_complex_args() {
        let mut program = create_test_program();

        let inlined_func = create_simple_function("inline_add", true);
        program
            .functions
            .insert("inline_add".to_string(), inlined_func);

        let caller_func = Function {
            name: "caller".to_string(),
            arguments: vec![("a".to_string(), false), ("b".to_string(), false)],
            inlined: false,
            body: vec![Line::FunctionCall(FunctionCall {
                function_name: "inline_add".to_string(),
                args: vec![
                    Expression::Binary {
                        left: Box::new(Expression::Value(SimpleExpr::Var("a".to_string()))),
                        operation: HighLevelOperation::Mul,
                        right: Box::new(Expression::Value(SimpleExpr::Constant(
                            ConstExpression::scalar(2),
                        ))),
                    },
                    Expression::Value(SimpleExpr::Var("b".to_string())),
                ],
                return_data: vec!["result".to_string()],
            })],
            n_returned_vars: 1,
        };
        program.functions.insert("caller".to_string(), caller_func);

        let mut pass = InlinePass::new();
        let result = pass.run(&mut program);

        assert!(result.is_ok());

        // Should create auxiliary variables for complex arguments
        let caller = program.functions.get("caller").unwrap();
        assert!(caller.body.len() >= 2); // At least one aux var assignment + inlined body
    }

    #[test]
    fn test_inline_pass_nested() {
        let mut program = create_test_program();

        // Create first inlined function
        let inline1 = Function {
            name: "inline1".to_string(),
            arguments: vec![("x".to_string(), false)],
            inlined: true,
            body: vec![Line::Assignment(Assignment {
                var: "temp".to_string(),
                value: Expression::Binary {
                    left: Box::new(Expression::Value(SimpleExpr::Var("x".to_string()))),
                    operation: HighLevelOperation::Add,
                    right: Box::new(Expression::Value(SimpleExpr::Constant(
                        ConstExpression::scalar(1),
                    ))),
                },
            })],
            n_returned_vars: 1,
        };
        program.functions.insert("inline1".to_string(), inline1);

        // Create second inlined function that calls the first
        let inline2 = Function {
            name: "inline2".to_string(),
            arguments: vec![("y".to_string(), false)],
            inlined: true,
            body: vec![Line::FunctionCall(FunctionCall {
                function_name: "inline1".to_string(),
                args: vec![Expression::Value(SimpleExpr::Var("y".to_string()))],
                return_data: vec!["result".to_string()],
            })],
            n_returned_vars: 1,
        };
        program.functions.insert("inline2".to_string(), inline2);

        // Create main function
        let main_func = Function {
            name: "main".to_string(),
            arguments: vec![("input".to_string(), false)],
            inlined: false,
            body: vec![Line::FunctionCall(FunctionCall {
                function_name: "inline2".to_string(),
                args: vec![Expression::Value(SimpleExpr::Var("input".to_string()))],
                return_data: vec!["output".to_string()],
            })],
            n_returned_vars: 1,
        };
        program.functions.insert("main".to_string(), main_func);

        let mut pass = InlinePass::new();
        let result = pass.run(&mut program);

        assert!(result.is_ok());

        // All inlined functions should be removed
        assert!(!program.functions.contains_key("inline1"));
        assert!(!program.functions.contains_key("inline2"));

        // Main function should contain the fully inlined code
        let main = program.functions.get("main").unwrap();
        assert!(!main.body.is_empty());
    }

    #[test]
    fn test_inline_pass_ssa_violation_repair() {
        let mut program = create_test_program();

        // Create an inlined function that has SSA violations
        let inlined_func = Function {
            name: "inline_cond".to_string(),
            arguments: vec![("x".to_string(), false)],
            inlined: true,
            body: vec![
                Line::IfCondition(IfCondition {
                    condition: Boolean::Equal {
                        left: Expression::Value(SimpleExpr::Var("x".to_string())),
                        right: Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(0))),
                    },
                    then_branch: vec![Line::FunctionRet(FunctionRet {
                        return_data: vec![Expression::Value(SimpleExpr::Constant(
                            ConstExpression::scalar(100),
                        ))],
                    })],
                    else_branch: vec![],
                }),
                Line::FunctionRet(FunctionRet {
                    return_data: vec![Expression::Value(SimpleExpr::Constant(
                        ConstExpression::scalar(200),
                    ))],
                }),
            ],
            n_returned_vars: 1,
        };
        program
            .functions
            .insert("inline_cond".to_string(), inlined_func);

        let caller_func = Function {
            name: "caller".to_string(),
            arguments: vec![("input".to_string(), false)],
            inlined: false,
            body: vec![Line::FunctionCall(FunctionCall {
                function_name: "inline_cond".to_string(),
                args: vec![Expression::Value(SimpleExpr::Var("input".to_string()))],
                return_data: vec!["result".to_string()],
            })],
            n_returned_vars: 1,
        };
        program.functions.insert("caller".to_string(), caller_func);

        let mut pass = InlinePass::new();
        let result = pass.run(&mut program);

        assert!(result.is_ok());

        // Should have properly handled SSA violations
        let caller = program.functions.get("caller").unwrap();
        assert!(!caller.body.is_empty());
    }
}
