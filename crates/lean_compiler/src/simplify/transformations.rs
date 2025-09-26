use super::utilities::replace_vars_by_const_in_lines;
use crate::{
    Counter,
    lang::{Boolean, Expression, Function, Line, Program, SimpleExpr, Var},
};
use std::collections::BTreeMap;

/// Handle inlined functions by replacing calls with function body.
pub fn handle_inlined_functions(program: &mut Program) {
    let inlined_functions = program
        .functions
        .iter()
        .filter(|(_, func)| func.inlined)
        .map(|(name, func)| (name.clone(), func.clone()))
        .collect::<BTreeMap<_, _>>();

    for func in inlined_functions.values() {
        assert!(
            !func.has_const_arguments(),
            "Inlined functions with constant arguments are not supported yet"
        );
    }

    // Process inline functions iteratively to handle dependencies
    // Repeat until all inline function calls are resolved
    let mut max_iterations = 10;
    while max_iterations > 0 {
        let mut any_changes = false;

        // Process non-inlined functions
        for func in program.functions.values_mut() {
            if !func.inlined {
                let mut counter1 = Counter::new();
                let mut counter2 = Counter::new();
                let old_body = func.body.clone();

                handle_inlined_functions_helper(
                    &mut func.body,
                    &inlined_functions,
                    &mut counter1,
                    &mut counter2,
                );

                if func.body != old_body {
                    any_changes = true;
                }
            }
        }

        // Process inlined functions that may call other inlined functions
        // We need to update them so that when they get inlined later, they don't have unresolved calls
        for func in program.functions.values_mut() {
            if func.inlined {
                let mut counter1 = Counter::new();
                let mut counter2 = Counter::new();
                let old_body = func.body.clone();

                handle_inlined_functions_helper(
                    &mut func.body,
                    &inlined_functions,
                    &mut counter1,
                    &mut counter2,
                );

                if func.body != old_body {
                    any_changes = true;
                }
            }
        }

        if !any_changes {
            break;
        }

        max_iterations -= 1;
    }

    assert!(
        max_iterations > 0,
        "Too many iterations processing inline functions"
    );

    // Remove all inlined functions from the program (they've been inlined)
    for func_name in inlined_functions.keys() {
        program.functions.remove(func_name);
    }
}

fn handle_inlined_functions_helper(
    lines: &mut Vec<Line>,
    inlined_functions: &BTreeMap<String, Function>,
    inlined_var_counter: &mut Counter,
    total_inlined_counter: &mut Counter,
) {
    for i in (0..lines.len()).rev() {
        match &mut lines[i] {
            Line::FunctionCall {
                function_name,
                args,
                return_data,
            } => {
                if let Some(func) = inlined_functions.get(&*function_name) {
                    let mut inlined_lines = vec![];

                    let mut simplified_args = vec![];
                    for arg in args {
                        if let Expression::Value(simple_expr) = arg {
                            simplified_args.push(simple_expr.clone());
                        } else {
                            let aux_var = format!("@inlined_var_{}", inlined_var_counter.next());
                            inlined_lines.push(Line::Assignment {
                                var: aux_var.clone(),
                                value: arg.clone(),
                            });
                            simplified_args.push(SimpleExpr::Var(aux_var));
                        }
                    }
                    assert_eq!(simplified_args.len(), func.arguments.len());
                    let inlined_args = func
                        .arguments
                        .iter()
                        .zip(&simplified_args)
                        .map(|((var, _), expr)| (var.clone(), expr.clone()))
                        .collect::<BTreeMap<_, _>>();
                    let mut func_body = func.body.clone();
                    inline_lines(
                        &mut func_body,
                        &inlined_args,
                        return_data,
                        total_inlined_counter.next(),
                    );
                    inlined_lines.extend(func_body);

                    lines.remove(i); // remove the call to the inlined function
                    lines.splice(i..i, inlined_lines);
                }
            }
            Line::IfCondition {
                then_branch,
                else_branch,
                ..
            } => {
                handle_inlined_functions_helper(
                    then_branch,
                    inlined_functions,
                    inlined_var_counter,
                    total_inlined_counter,
                );
                handle_inlined_functions_helper(
                    else_branch,
                    inlined_functions,
                    inlined_var_counter,
                    total_inlined_counter,
                );
            }
            Line::ForLoop {
                body, unroll: _, ..
            } => {
                handle_inlined_functions_helper(
                    body,
                    inlined_functions,
                    inlined_var_counter,
                    total_inlined_counter,
                );
            }
            Line::Match { arms, .. } => {
                for (_, arm) in arms {
                    handle_inlined_functions_helper(
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

/// Handle functions with constant arguments by creating specialized versions.
pub fn handle_const_arguments(program: &mut Program) {
    let mut new_functions = BTreeMap::<String, Function>::new();
    let constant_functions = program
        .functions
        .iter()
        .filter(|(_, func)| func.has_const_arguments())
        .map(|(name, func)| (name.clone(), func.clone()))
        .collect::<BTreeMap<_, _>>();

    // First pass: process non-const functions that call const functions
    for func in program.functions.values_mut() {
        if !func.has_const_arguments() {
            handle_const_arguments_helper(&mut func.body, &constant_functions, &mut new_functions);
        }
    }

    // Process newly created const functions recursively until no more changes
    let mut changed = true;
    let mut const_depth = 0;
    while changed {
        changed = false;
        const_depth += 1;
        assert!(const_depth < 100, "Too many levels of constant arguments");
        let mut additional_functions = BTreeMap::new();

        // Collect all function names to process
        let function_names: Vec<String> = new_functions.keys().cloned().collect();

        for name in function_names {
            if let Some(func) = new_functions.get_mut(&name) {
                let initial_count = additional_functions.len();
                handle_const_arguments_helper(
                    &mut func.body,
                    &constant_functions,
                    &mut additional_functions,
                );
                if additional_functions.len() > initial_count {
                    changed = true;
                }
            }
        }

        // Add any newly discovered functions
        for (name, func) in additional_functions {
            if let std::collections::btree_map::Entry::Vacant(e) = new_functions.entry(name) {
                e.insert(func);
                changed = true;
            }
        }
    }

    for (name, func) in new_functions {
        assert!(!program.functions.contains_key(&name),);
        program.functions.insert(name, func);
    }
    for const_func in constant_functions.keys() {
        program.functions.remove(const_func);
    }
}

fn handle_const_arguments_helper(
    lines: &mut [Line],
    constant_functions: &BTreeMap<String, Function>,
    new_functions: &mut BTreeMap<String, Function>,
) {
    for line in lines {
        match line {
            Line::FunctionCall {
                function_name,
                args,
                return_data: _,
            } => {
                if let Some(func) = constant_functions.get(function_name) {
                    // If the function has constant arguments, we need to handle them
                    let mut const_evals = Vec::new();
                    for (arg_expr, (arg_var, is_constant)) in args.iter().zip(&func.arguments) {
                        if *is_constant {
                            let const_eval = arg_expr.naive_eval().unwrap_or_else(|| {
                                panic!("Failed to evaluate constant argument: {arg_expr}")
                            });
                            const_evals.push((arg_var.clone(), const_eval));
                        }
                    }
                    let const_funct_name = format!(
                        "{function_name}_{}",
                        const_evals
                            .iter()
                            .map(|(arg_var, const_eval)| { format!("{arg_var}={const_eval}") })
                            .collect::<Vec<_>>()
                            .join("_")
                    );

                    *function_name = const_funct_name.clone(); // change the name of the function called
                    // ... and remove constant arguments
                    *args = args
                        .iter()
                        .zip(&func.arguments)
                        .filter(|(_, (_, is_constant))| !is_constant)
                        .filter(|(_, (_, is_const))| !is_const)
                        .map(|(arg_expr, _)| arg_expr.clone())
                        .collect();

                    if new_functions.contains_key(&const_funct_name) {
                        continue;
                    }

                    let mut new_body = func.body.clone();
                    replace_vars_by_const_in_lines(
                        &mut new_body,
                        &const_evals.iter().cloned().collect(),
                    );
                    new_functions.insert(
                        const_funct_name.clone(),
                        Function {
                            name: const_funct_name,
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
            Line::IfCondition {
                then_branch,
                else_branch,
                ..
            } => {
                handle_const_arguments_helper(then_branch, constant_functions, new_functions);
                handle_const_arguments_helper(else_branch, constant_functions, new_functions);
            }
            Line::ForLoop {
                body, unroll: _, ..
            } => {
                // TODO we should unroll before const arguments handling
                handle_const_arguments_helper(body, constant_functions, new_functions);
            }
            _ => {}
        }
    }
}

/// Inline function bodies at call sites.
pub fn inline_lines(
    lines: &mut Vec<Line>,
    args: &BTreeMap<Var, SimpleExpr>,
    res: &[Var],
    inlining_count: usize,
) {
    let inline_condition = |condition: &mut Boolean| {
        let (Boolean::Equal { left, right } | Boolean::Different { left, right }) = condition;
        inline_expr(left, args, inlining_count);
        inline_expr(right, args, inlining_count);
    };

    let inline_internal_var = |var: &mut Var| {
        assert!(
            !args.contains_key(var),
            "Variable {var} is both an argument and assigned in the inlined function"
        );
        *var = format!("@inlined_var_{inlining_count}_{var}");
    };

    let mut lines_to_replace = vec![];
    for (i, line) in lines.iter_mut().enumerate() {
        match line {
            Line::Match { value, arms } => {
                inline_expr(value, args, inlining_count);
                for (_, statements) in arms {
                    inline_lines(statements, args, res, inlining_count);
                }
            }
            Line::Assignment { var, value } => {
                inline_expr(value, args, inlining_count);
                inline_internal_var(var);
            }
            Line::IfCondition {
                condition,
                then_branch,
                else_branch,
            } => {
                inline_condition(condition);

                inline_lines(then_branch, args, res, inlining_count);
                inline_lines(else_branch, args, res, inlining_count);
            }
            Line::FunctionCall {
                args: func_args,
                return_data,
                ..
            } => {
                for arg in func_args {
                    inline_expr(arg, args, inlining_count);
                }
                for return_var in return_data {
                    inline_internal_var(return_var);
                }
            }
            Line::Assert(condition) => {
                inline_condition(condition);
            }
            Line::FunctionRet { return_data } => {
                assert_eq!(return_data.len(), res.len());

                for expr in return_data.iter_mut() {
                    inline_expr(expr, args, inlining_count);
                }
                lines_to_replace.push((
                    i,
                    res.iter()
                        .zip(return_data)
                        .map(|(res_var, expr)| Line::Assignment {
                            var: res_var.clone(),
                            value: expr.clone(),
                        })
                        .collect::<Vec<_>>(),
                ));
            }
            Line::MAlloc { var, size, .. } => {
                inline_expr(size, args, inlining_count);
                inline_internal_var(var);
            }
            Line::Precompile {
                precompile: _,
                args: precompile_args,
            } => {
                for arg in precompile_args {
                    inline_expr(arg, args, inlining_count);
                }
            }
            Line::Print { content, .. } => {
                for var in content {
                    inline_expr(var, args, inlining_count);
                }
            }
            Line::DecomposeBits { var, to_decompose } => {
                for expr in to_decompose {
                    inline_expr(expr, args, inlining_count);
                }
                inline_internal_var(var);
            }
            Line::CounterHint { var } => {
                inline_internal_var(var);
            }
            Line::ForLoop {
                iterator,
                start,
                end,
                body,
                rev: _,
                unroll: _,
            } => {
                inline_lines(body, args, res, inlining_count);
                inline_internal_var(iterator);
                inline_expr(start, args, inlining_count);
                inline_expr(end, args, inlining_count);
            }
            Line::ArrayAssign {
                array,
                index,
                value,
            } => {
                inline_simple_expr(array, args, inlining_count);
                inline_expr(index, args, inlining_count);
                inline_expr(value, args, inlining_count);
            }
            Line::Panic | Line::Break | Line::LocationReport { .. } => {}
        }
    }
    for (i, new_lines) in lines_to_replace.into_iter().rev() {
        lines.splice(i..=i, new_lines);
    }
}

fn inline_expr(expr: &mut Expression, args: &BTreeMap<Var, SimpleExpr>, inlining_count: usize) {
    match expr {
        Expression::Value(value) => {
            inline_simple_expr(value, args, inlining_count);
        }
        Expression::ArrayAccess { array, index } => {
            inline_simple_expr(array, args, inlining_count);
            inline_expr(index, args, inlining_count);
        }
        Expression::Binary { left, right, .. } => {
            inline_expr(left, args, inlining_count);
            inline_expr(right, args, inlining_count);
        }
        Expression::Log2Ceil { value } => {
            inline_expr(value, args, inlining_count);
        }
    }
}

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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ir::HighLevelOperation, lang::*};

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
            body: vec![Line::Assignment {
                var: "result".to_string(),
                value: Expression::Binary {
                    left: Box::new(Expression::Value(SimpleExpr::Var("x".to_string()))),
                    operation: HighLevelOperation::Add,
                    right: Box::new(Expression::Value(SimpleExpr::Var("y".to_string()))),
                },
            }],
            n_returned_vars: 1,
        }
    }

    fn create_const_function(name: &str) -> Function {
        Function {
            name: name.to_string(),
            arguments: vec![("x".to_string(), false), ("size".to_string(), true)],
            inlined: false,
            body: vec![Line::Assignment {
                var: "result".to_string(),
                value: Expression::Binary {
                    left: Box::new(Expression::Value(SimpleExpr::Var("x".to_string()))),
                    operation: HighLevelOperation::Add,
                    right: Box::new(Expression::Value(SimpleExpr::Var("size".to_string()))),
                },
            }],
            n_returned_vars: 1,
        }
    }

    #[test]
    fn test_handle_inlined_functions_simple_inline() {
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
            body: vec![Line::FunctionCall {
                function_name: "inline_add".to_string(),
                args: vec![
                    Expression::Value(SimpleExpr::Var("a".to_string())),
                    Expression::Value(SimpleExpr::Var("b".to_string())),
                ],
                return_data: vec!["sum".to_string()],
            }],
            n_returned_vars: 1,
        };
        program.functions.insert("caller".to_string(), caller_func);

        handle_inlined_functions(&mut program);

        // The inlined function should be removed
        assert!(!program.functions.contains_key("inline_add"));

        // The caller function should have the inlined code
        let caller = program.functions.get("caller").unwrap();
        assert_eq!(caller.body.len(), 1);
        if let Line::Assignment { var, value } = &caller.body[0] {
            assert!(var.starts_with("@inlined_var_"));
            if let Expression::Binary {
                left,
                operation,
                right,
            } = value
            {
                assert_eq!(operation, &HighLevelOperation::Add);
                if let Expression::Value(SimpleExpr::Var(left_var)) = left.as_ref() {
                    assert_eq!(left_var, "a");
                }
                if let Expression::Value(SimpleExpr::Var(right_var)) = right.as_ref() {
                    assert_eq!(right_var, "b");
                }
            }
        }
    }

    #[test]
    fn test_handle_inlined_functions_complex_args() {
        let mut program = create_test_program();

        // Create an inlined function
        let inlined_func = create_simple_function("inline_add", true);
        program
            .functions
            .insert("inline_add".to_string(), inlined_func);

        // Create a function that calls the inlined function with complex arguments
        let caller_func = Function {
            name: "caller".to_string(),
            arguments: vec![("a".to_string(), false), ("b".to_string(), false)],
            inlined: false,
            body: vec![Line::FunctionCall {
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
            }],
            n_returned_vars: 1,
        };
        program.functions.insert("caller".to_string(), caller_func);

        handle_inlined_functions(&mut program);

        // Check that auxiliary variables are created for complex arguments
        let caller = program.functions.get("caller").unwrap();
        assert!(caller.body.len() >= 2); // At least one aux var assignment + the inlined body

        // First instruction should be auxiliary variable assignment for complex argument
        if let Line::Assignment { var, value } = &caller.body[0] {
            assert!(var.starts_with("@inlined_var_"));
            if let Expression::Binary { operation, .. } = value {
                assert_eq!(operation, &HighLevelOperation::Mul);
            }
        }
    }

    #[test]
    fn test_handle_inlined_functions_nested_inline() {
        let mut program = create_test_program();

        // Create first inlined function
        let inline1 = Function {
            name: "inline1".to_string(),
            arguments: vec![("x".to_string(), false)],
            inlined: true,
            body: vec![Line::Assignment {
                var: "temp".to_string(),
                value: Expression::Binary {
                    left: Box::new(Expression::Value(SimpleExpr::Var("x".to_string()))),
                    operation: HighLevelOperation::Add,
                    right: Box::new(Expression::Value(SimpleExpr::Constant(
                        ConstExpression::scalar(1),
                    ))),
                },
            }],
            n_returned_vars: 1,
        };
        program.functions.insert("inline1".to_string(), inline1);

        // Create second inlined function that calls the first
        let inline2 = Function {
            name: "inline2".to_string(),
            arguments: vec![("y".to_string(), false)],
            inlined: true,
            body: vec![Line::FunctionCall {
                function_name: "inline1".to_string(),
                args: vec![Expression::Value(SimpleExpr::Var("y".to_string()))],
                return_data: vec!["result".to_string()],
            }],
            n_returned_vars: 1,
        };
        program.functions.insert("inline2".to_string(), inline2);

        // Create main function that calls inline2
        let main_func = Function {
            name: "main".to_string(),
            arguments: vec![("input".to_string(), false)],
            inlined: false,
            body: vec![Line::FunctionCall {
                function_name: "inline2".to_string(),
                args: vec![Expression::Value(SimpleExpr::Var("input".to_string()))],
                return_data: vec!["output".to_string()],
            }],
            n_returned_vars: 1,
        };
        program.functions.insert("main".to_string(), main_func);

        handle_inlined_functions(&mut program);

        // All inlined functions should be removed
        assert!(!program.functions.contains_key("inline1"));
        assert!(!program.functions.contains_key("inline2"));

        // Main function should contain the fully inlined code
        let main = program.functions.get("main").unwrap();
        assert!(!main.body.is_empty());

        // Should have the actual computation inlined
        let has_add_op = main.body.iter().any(|line| {
            if let Line::Assignment { value, .. } = line
                && let Expression::Binary { operation, .. } = value
            {
                return *operation == HighLevelOperation::Add;
            }
            false
        });
        assert!(has_add_op);
    }

    #[test]
    fn test_handle_inlined_functions_if_condition() {
        let mut program = create_test_program();

        // Create an inlined function
        let inlined_func = create_simple_function("inline_add", true);
        program
            .functions
            .insert("inline_add".to_string(), inlined_func);

        // Create a function that calls the inlined function inside an if condition
        let caller_func = Function {
            name: "caller".to_string(),
            arguments: vec![("condition".to_string(), false)],
            inlined: false,
            body: vec![Line::IfCondition {
                condition: Boolean::Equal {
                    left: Expression::Value(SimpleExpr::Var("condition".to_string())),
                    right: Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(1))),
                },
                then_branch: vec![Line::FunctionCall {
                    function_name: "inline_add".to_string(),
                    args: vec![
                        Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(5))),
                        Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(3))),
                    ],
                    return_data: vec!["result".to_string()],
                }],
                else_branch: vec![],
            }],
            n_returned_vars: 0,
        };
        program.functions.insert("caller".to_string(), caller_func);

        handle_inlined_functions(&mut program);

        // Check that the function call is inlined inside the if condition
        let caller = program.functions.get("caller").unwrap();
        if let Line::IfCondition { then_branch, .. } = &caller.body[0] {
            assert!(!then_branch.is_empty());
            // Should have inlined assignment
            if let Line::Assignment { .. } = &then_branch[0] {
                // Good, the function was inlined
            } else {
                panic!("Expected inlined assignment in then branch");
            }
        } else {
            panic!("Expected if condition");
        }
    }

    #[test]
    #[should_panic(expected = "Too many iterations processing inline functions")]
    fn test_handle_inlined_functions_infinite_recursion() {
        let mut program = create_test_program();

        // Create an inlined function A that calls inlined function B
        let func_a = Function {
            name: "func_a".to_string(),
            arguments: vec![("x".to_string(), false)],
            inlined: true,
            body: vec![Line::FunctionCall {
                function_name: "func_b".to_string(),
                args: vec![Expression::Value(SimpleExpr::Var("x".to_string()))],
                return_data: vec!["result".to_string()],
            }],
            n_returned_vars: 1,
        };

        // Create an inlined function B that calls inlined function A (mutual recursion)
        let func_b = Function {
            name: "func_b".to_string(),
            arguments: vec![("x".to_string(), false)],
            inlined: true,
            body: vec![Line::FunctionCall {
                function_name: "func_a".to_string(),
                args: vec![Expression::Value(SimpleExpr::Var("x".to_string()))],
                return_data: vec!["result".to_string()],
            }],
            n_returned_vars: 1,
        };

        program.functions.insert("func_a".to_string(), func_a);
        program.functions.insert("func_b".to_string(), func_b);

        // Create main function that calls func_a (which will trigger the mutual recursion)
        let main_func = Function {
            name: "main".to_string(),
            arguments: vec![],
            inlined: false,
            body: vec![Line::FunctionCall {
                function_name: "func_a".to_string(),
                args: vec![Expression::Value(SimpleExpr::Constant(
                    ConstExpression::scalar(1),
                ))],
                return_data: vec!["result".to_string()],
            }],
            n_returned_vars: 1,
        };
        program.functions.insert("main".to_string(), main_func);

        // This should panic due to infinite mutual recursion detection
        handle_inlined_functions(&mut program);
    }

    #[test]
    fn test_handle_const_arguments_simple() {
        let mut program = create_test_program();

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
            body: vec![Line::FunctionCall {
                function_name: "const_func".to_string(),
                args: vec![
                    Expression::Value(SimpleExpr::Var("input".to_string())),
                    Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(10))),
                ],
                return_data: vec!["result".to_string()],
            }],
            n_returned_vars: 1,
        };
        program.functions.insert("caller".to_string(), caller_func);

        handle_const_arguments(&mut program);

        // Original const function should be removed
        assert!(!program.functions.contains_key("const_func"));

        // Should have a new specialized function
        let specialized_name = "const_func_size=10";
        assert!(program.functions.contains_key(specialized_name));

        // Caller should call the specialized function
        let caller = program.functions.get("caller").unwrap();
        if let Line::FunctionCall {
            function_name,
            args,
            ..
        } = &caller.body[0]
        {
            assert_eq!(function_name, specialized_name);
            assert_eq!(args.len(), 1); // Only non-const arguments
        }
    }

    #[test]
    fn test_handle_const_arguments_multiple_values() {
        let mut program = create_test_program();

        let const_func = create_const_function("const_func");
        program
            .functions
            .insert("const_func".to_string(), const_func);

        // Create two callers with different constant values
        let caller1 = Function {
            name: "caller1".to_string(),
            arguments: vec![("input".to_string(), false)],
            inlined: false,
            body: vec![Line::FunctionCall {
                function_name: "const_func".to_string(),
                args: vec![
                    Expression::Value(SimpleExpr::Var("input".to_string())),
                    Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(5))),
                ],
                return_data: vec!["result1".to_string()],
            }],
            n_returned_vars: 1,
        };
        program.functions.insert("caller1".to_string(), caller1);

        let caller2 = Function {
            name: "caller2".to_string(),
            arguments: vec![("input".to_string(), false)],
            inlined: false,
            body: vec![Line::FunctionCall {
                function_name: "const_func".to_string(),
                args: vec![
                    Expression::Value(SimpleExpr::Var("input".to_string())),
                    Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(10))),
                ],
                return_data: vec!["result2".to_string()],
            }],
            n_returned_vars: 1,
        };
        program.functions.insert("caller2".to_string(), caller2);

        handle_const_arguments(&mut program);

        // Should have two specialized functions
        assert!(program.functions.contains_key("const_func_size=5"));
        assert!(program.functions.contains_key("const_func_size=10"));
        assert!(!program.functions.contains_key("const_func"));

        // Callers should reference the correct specialized functions
        let caller1 = program.functions.get("caller1").unwrap();
        if let Line::FunctionCall { function_name, .. } = &caller1.body[0] {
            assert_eq!(function_name, "const_func_size=5");
        }

        let caller2 = program.functions.get("caller2").unwrap();
        if let Line::FunctionCall { function_name, .. } = &caller2.body[0] {
            assert_eq!(function_name, "const_func_size=10");
        }
    }

    #[test]
    fn test_inline_lines_assignment() {
        let mut lines = vec![Line::Assignment {
            var: "x".to_string(),
            value: Expression::Value(SimpleExpr::Var("arg1".to_string())),
        }];

        let mut args = BTreeMap::new();
        args.insert(
            "arg1".to_string(),
            SimpleExpr::Constant(ConstExpression::scalar(42)),
        );

        let res = vec!["result".to_string()];

        inline_lines(&mut lines, &args, &res, 0);

        // Variable should be renamed and argument replaced
        if let Line::Assignment { var, value } = &lines[0] {
            assert_eq!(var, "@inlined_var_0_x");
            if let Expression::Value(SimpleExpr::Constant(const_expr)) = value {
                assert_eq!(const_expr, &ConstExpression::scalar(42));
            } else {
                panic!("Expected constant value");
            }
        }
    }

    #[test]
    fn test_inline_lines_function_return() {
        let mut lines = vec![Line::FunctionRet {
            return_data: vec![
                Expression::Value(SimpleExpr::Var("local_var".to_string())),
                Expression::Value(SimpleExpr::Var("arg1".to_string())),
            ],
        }];

        let mut args = BTreeMap::new();
        args.insert("arg1".to_string(), SimpleExpr::Var("input".to_string()));

        let res = vec!["output1".to_string(), "output2".to_string()];

        inline_lines(&mut lines, &args, &res, 1);

        // Function return should be converted to assignments
        assert_eq!(lines.len(), 2);

        if let Line::Assignment { var, value } = &lines[0] {
            assert_eq!(var, "output1");
            if let Expression::Value(SimpleExpr::Var(var_name)) = value {
                assert_eq!(var_name, "@inlined_var_1_local_var");
            } else {
                panic!("Expected variable value in first assignment");
            }
        } else {
            panic!("Expected assignment in first line");
        }

        if let Line::Assignment { var, value } = &lines[1] {
            assert_eq!(var, "output2");
            if let Expression::Value(SimpleExpr::Var(var_name)) = value {
                assert_eq!(var_name, "input");
            } else {
                panic!("Expected variable value in second assignment");
            }
        } else {
            panic!("Expected assignment in second line");
        }
    }

    #[test]
    fn test_inline_lines_if_condition() {
        let mut lines = vec![Line::IfCondition {
            condition: Boolean::Equal {
                left: Expression::Value(SimpleExpr::Var("arg1".to_string())),
                right: Expression::Value(SimpleExpr::Var("local_var".to_string())),
            },
            then_branch: vec![Line::Assignment {
                var: "then_var".to_string(),
                value: Expression::Value(SimpleExpr::Var("arg1".to_string())),
            }],
            else_branch: vec![Line::Assignment {
                var: "else_var".to_string(),
                value: Expression::Value(SimpleExpr::Var("local_var".to_string())),
            }],
        }];

        let mut args = BTreeMap::new();
        args.insert("arg1".to_string(), SimpleExpr::Var("input".to_string()));

        let res = vec![];

        inline_lines(&mut lines, &args, &res, 2);

        if let Line::IfCondition {
            condition,
            then_branch,
            else_branch,
        } = &lines[0]
        {
            // Condition variables should be inlined
            if let Boolean::Equal { left, right } = condition {
                if let Expression::Value(SimpleExpr::Var(left_var)) = left {
                    assert_eq!(left_var, "input");
                } else {
                    panic!("Expected variable in left side of condition");
                }
                if let Expression::Value(SimpleExpr::Var(right_var)) = right {
                    assert_eq!(right_var, "@inlined_var_2_local_var");
                } else {
                    panic!("Expected variable in right side of condition");
                }
            } else {
                panic!("Expected Equal condition");
            }

            // Variables in branches should be renamed
            if let Line::Assignment { var, value } = &then_branch[0] {
                assert_eq!(var, "@inlined_var_2_then_var");
                if let Expression::Value(SimpleExpr::Var(val_var)) = value {
                    assert_eq!(val_var, "input");
                } else {
                    panic!("Expected variable value in then branch assignment");
                }
            } else {
                panic!("Expected assignment in then branch");
            }

            if let Line::Assignment { var, value } = &else_branch[0] {
                assert_eq!(var, "@inlined_var_2_else_var");
                if let Expression::Value(SimpleExpr::Var(val_var)) = value {
                    assert_eq!(val_var, "@inlined_var_2_local_var");
                } else {
                    panic!("Expected variable value in else branch assignment");
                }
            } else {
                panic!("Expected assignment in else branch");
            }
        } else {
            panic!("Expected if condition");
        }
    }

    #[test]
    fn test_inline_lines_for_loop() {
        let mut lines = vec![Line::ForLoop {
            iterator: "i".to_string(),
            start: Expression::Value(SimpleExpr::Var("arg1".to_string())),
            end: Expression::Value(SimpleExpr::Var("local_end".to_string())),
            body: vec![Line::Assignment {
                var: "loop_var".to_string(),
                value: Expression::Value(SimpleExpr::Var("i".to_string())),
            }],
            rev: false,
            unroll: false,
        }];

        let mut args = BTreeMap::new();
        args.insert(
            "arg1".to_string(),
            SimpleExpr::Constant(ConstExpression::scalar(0)),
        );

        let res = vec![];

        inline_lines(&mut lines, &args, &res, 3);

        if let Line::ForLoop {
            iterator,
            start,
            end,
            body,
            ..
        } = &lines[0]
        {
            // Iterator should be renamed
            assert_eq!(iterator, "@inlined_var_3_i");

            // Start expression should use inlined argument
            if let Expression::Value(SimpleExpr::Constant(const_expr)) = start {
                assert_eq!(const_expr, &ConstExpression::scalar(0));
            } else {
                panic!("Expected constant start value in for loop");
            }

            // End variable should be renamed
            if let Expression::Value(SimpleExpr::Var(end_var)) = end {
                assert_eq!(end_var, "@inlined_var_3_local_end");
            } else {
                panic!("Expected variable end value in for loop");
            }

            // Body variables should be renamed
            if let Line::Assignment { var, .. } = &body[0] {
                assert_eq!(var, "@inlined_var_3_loop_var");
            } else {
                panic!("Expected assignment in for loop body");
            }
        } else {
            panic!("Expected for loop");
        }
    }
}
