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
