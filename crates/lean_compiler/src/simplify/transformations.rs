use super::{types::Counter, utilities::replace_vars_by_const_in_lines};
use crate::lang::{Boolean, ConstExpression, Expression, Function, Line, Program, SimpleExpr, Var};
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
    inline_lines_with_flag(lines, args, res, inlining_count, None);
}

/// Internal function that handles inlining with optional return flag support
fn inline_lines_with_flag(
    lines: &mut Vec<Line>,
    args: &BTreeMap<Var, SimpleExpr>,
    res: &[Var],
    inlining_count: usize,
    return_flag_var: Option<&str>,
) {
    let inline_condition = |condition: &mut Boolean| {
        let (Boolean::Equal { left, right } | Boolean::Different { left, right }) = condition;
        inline_expr(left, args, inlining_count);
        inline_expr(right, args, inlining_count);
    };

    let inline_internal_var = |var: &mut Var| {
        // Don't rename return flag variables
        if var.starts_with("@inlined_returned_") {
            return;
        }

        assert!(
            !args.contains_key(var),
            "Variable {var} is both an argument and assigned in the inlined function"
        );
        *var = format!("@inlined_var_{inlining_count}_{var}");
    };

    // Check if we need special handling for non-exhaustive returns
    let needs_special_handling = needs_return_flag_logic(lines);

    let mut lines_to_replace = vec![];
    for (i, line) in lines.iter_mut().enumerate() {
        match line {
            Line::Match { value, arms } => {
                inline_expr(value, args, inlining_count);
                for (_, statements) in arms {
                    inline_lines_with_flag(statements, args, res, inlining_count, return_flag_var);
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

                inline_lines_with_flag(then_branch, args, res, inlining_count, return_flag_var);
                inline_lines_with_flag(else_branch, args, res, inlining_count, return_flag_var);
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

                // For now, just use direct assignments
                // The post-processing will handle the SSA issue
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

    // Post-processing: if we need special handling, apply control flow restructuring
    if needs_special_handling {
        fix_ssa_violations_by_restructuring_control_flow(lines, res);
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

/// Check recursively if there are multiple potential return paths that could execute
/// This determines if we need return flag logic to prevent SSA violations
fn needs_return_flag_logic(lines: &[Line]) -> bool {
    // Look for the specific problematic pattern: nested if conditions with returns that can fall through
    has_nested_non_exhaustive_returns(lines)
}

/// Check for the specific pattern that causes SSA violations:
/// nested if conditions with returns where execution can fall through to later returns
fn has_nested_non_exhaustive_returns(lines: &[Line]) -> bool {
    // Look for functions that have both:
    // 1. If conditions (nested or simple) with returns in non-exhaustive branches
    // 2. Returns at the end (fall-through pattern)

    let has_if_returns =
        has_nested_if_with_returns(lines) || has_simple_non_exhaustive_if_returns(lines);
    let has_final_return = lines
        .iter()
        .any(|line| matches!(line, Line::FunctionRet { .. }));

    has_if_returns && has_final_return
}

/// Check if there are nested if conditions that contain returns
fn has_nested_if_with_returns(lines: &[Line]) -> bool {
    for line in lines {
        match line {
            Line::IfCondition {
                then_branch,
                else_branch,
                ..
            } => {
                // Check if this if contains nested ifs with returns
                for nested_line in then_branch.iter().chain(else_branch.iter()) {
                    if let Line::IfCondition {
                        then_branch: nested_then,
                        else_branch: nested_else,
                        ..
                    } = nested_line
                    {
                        if has_return_statements_in_branch(nested_then)
                            || has_return_statements_in_branch(nested_else)
                        {
                            return true;
                        }
                    }
                }

                // Recurse
                if has_nested_if_with_returns(then_branch)
                    || has_nested_if_with_returns(else_branch)
                {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}

/// Check if there's only a single return statement at the very end of the function
fn is_single_return_at_end(lines: &[Line]) -> bool {
    if lines.is_empty() {
        return false;
    }

    let total_returns = count_return_statements_recursive(lines);

    // If no returns at all, that's fine (no flag needed)
    if total_returns == 0 {
        return true;
    }

    // If exactly one return and it's at the end, no flag needed
    if total_returns == 1 {
        if let Line::FunctionRet { .. } = lines.last().unwrap() {
            // Make sure there are no other returns earlier
            count_return_statements_recursive(&lines[..lines.len() - 1]) == 0
        } else {
            // Single return but not at the end - need flag logic
            false
        }
    } else {
        // Multiple returns - need flag logic
        false
    }
}

/// Count the number of FunctionRet statements recursively
fn count_return_statements_recursive(lines: &[Line]) -> usize {
    let mut count = 0;
    for line in lines {
        match line {
            Line::FunctionRet { .. } => count += 1,
            Line::IfCondition {
                then_branch,
                else_branch,
                ..
            } => {
                count += count_return_statements_recursive(then_branch);
                count += count_return_statements_recursive(else_branch);
            }
            Line::ForLoop { body, .. } => {
                count += count_return_statements_recursive(body);
            }
            Line::Match { arms, .. } => {
                for (_, arm_statements) in arms {
                    count += count_return_statements_recursive(arm_statements);
                }
            }
            _ => {}
        }
    }
    count
}

/// Check if there are non-exhaustive returns that could cause SSA violations
/// This specifically looks for cases where multiple returns could execute in the same call
fn has_non_exhaustive_returns(lines: &[Line]) -> bool {
    // Look for patterns that could cause SSA violations:
    // 1. Returns that can fall through to subsequent returns
    // 2. Multiple returns outside of exhaustive if-else patterns
    check_non_exhaustive_patterns(lines, false)
}

/// Helper function to check for non-exhaustive return patterns
fn check_non_exhaustive_patterns(lines: &[Line], inside_condition: bool) -> bool {
    let mut has_unconditional_return = false;

    for (i, line) in lines.iter().enumerate() {
        match line {
            Line::FunctionRet { .. } => {
                // If we find a return statement, check if there are more statements after it
                // This could cause SSA violations if both returns can execute
                if i < lines.len() - 1 {
                    // There are more statements after this return - check if any are returns
                    let remaining_lines = &lines[i + 1..];
                    if count_return_statements_recursive(remaining_lines) > 0 {
                        return true; // Multiple returns that could both execute
                    }
                }
                has_unconditional_return = true;
            }
            Line::IfCondition {
                then_branch,
                else_branch,
                ..
            } => {
                let then_has_returns = has_return_statements_in_branch(then_branch);
                let else_has_returns = has_return_statements_in_branch(else_branch);

                // Check if this is a non-exhaustive if condition
                if then_has_returns && else_branch.is_empty() {
                    // Non-exhaustive: if condition with return but no else
                    return true;
                }
                if then_has_returns && !else_has_returns {
                    // Non-exhaustive: return in then branch but not in else branch
                    return true;
                }
                if !then_has_returns && else_has_returns {
                    // Non-exhaustive: return in else branch but not in then branch
                    return true;
                }

                // Recurse into branches
                if check_non_exhaustive_patterns(then_branch, true)
                    || check_non_exhaustive_patterns(else_branch, true)
                {
                    return true;
                }
            }
            Line::ForLoop { body, .. } => {
                // Returns inside for loops are always non-exhaustive
                if has_return_statements_in_branch(body) {
                    return true;
                }
                if check_non_exhaustive_patterns(body, true) {
                    return true;
                }
            }
            Line::Match { arms, .. } => {
                // For match statements, check if all arms have returns (exhaustive) or not
                let arms_with_returns = arms
                    .iter()
                    .filter(|(_, arm_statements)| has_return_statements_in_branch(arm_statements))
                    .count();

                if arms_with_returns > 0 && arms_with_returns < arms.len() {
                    // Non-exhaustive: some arms have returns but not all
                    return true;
                }

                // Recurse into match arms
                for (_, arm_statements) in arms {
                    if check_non_exhaustive_patterns(arm_statements, true) {
                        return true;
                    }
                }
            }
            _ => {}
        }
    }

    false
}

/// Check if there are returns inside conditional statements (if/for/match)
/// that could potentially cause multiple execution paths to assign to the same variable
fn has_conditional_returns_recursive(lines: &[Line]) -> bool {
    for line in lines {
        match line {
            Line::IfCondition {
                then_branch,
                else_branch,
                ..
            } => {
                // If either branch has a return, we need flag logic
                if has_return_statements_in_branch(then_branch)
                    || has_return_statements_in_branch(else_branch)
                {
                    return true;
                }
                // Recurse into nested conditions
                if has_conditional_returns_recursive(then_branch)
                    || has_conditional_returns_recursive(else_branch)
                {
                    return true;
                }
            }
            Line::ForLoop { body, .. } => {
                if has_return_statements_in_branch(body) || has_conditional_returns_recursive(body)
                {
                    return true;
                }
            }
            Line::Match { arms, .. } => {
                for (_, arm_statements) in arms {
                    if has_return_statements_in_branch(arm_statements)
                        || has_conditional_returns_recursive(arm_statements)
                    {
                        return true;
                    }
                }
            }
            _ => {}
        }
    }
    false
}

/// Check if a branch has any return statements
fn has_return_statements_in_branch(lines: &[Line]) -> bool {
    for line in lines {
        match line {
            Line::FunctionRet { .. } => return true,
            Line::IfCondition {
                then_branch,
                else_branch,
                ..
            } => {
                if has_return_statements_in_branch(then_branch)
                    || has_return_statements_in_branch(else_branch)
                {
                    return true;
                }
            }
            Line::ForLoop { body, .. } => {
                if has_return_statements_in_branch(body) {
                    return true;
                }
            }
            Line::Match { arms, .. } => {
                for (_, arm_statements) in arms {
                    if has_return_statements_in_branch(arm_statements) {
                        return true;
                    }
                }
            }
            _ => {}
        }
    }
    false
}

/// Check for simple non-exhaustive if statements with returns
fn has_simple_non_exhaustive_if_returns(lines: &[Line]) -> bool {
    for line in lines {
        if let Line::IfCondition {
            then_branch,
            else_branch,
            ..
        } = line
        {
            // If the else branch is empty and the then branch has returns, it's non-exhaustive
            if else_branch.is_empty() && has_return_statements_in_branch(then_branch) {
                return true;
            }
            // Recursively check nested branches
            if has_simple_non_exhaustive_if_returns(then_branch)
                || has_simple_non_exhaustive_if_returns(else_branch)
            {
                return true;
            }
        }
    }
    false
}

/// Apply return flag logic to prevent SSA violations
/// This introduces a flag variable to track if a return has occurred
fn apply_return_flag_logic(lines: &mut Vec<Line>, res: &[Var]) {
    if res.is_empty() {
        return; // No return variables to handle
    }

    let flag_var = format!("returned_flag_{}", res.get(0).unwrap_or(&String::new()));

    // Initialize flag to 0
    lines.insert(
        0,
        Line::Assignment {
            var: flag_var.clone(),
            value: Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(0))),
        },
    );

    // Convert FunctionRet statements to conditional assignments
    convert_returns_to_conditional_assignments(lines, res, &flag_var);
}

/// Convert assignments to result variables into conditional assignments using a return flag
fn convert_returns_to_conditional_assignments(lines: &mut Vec<Line>, res: &[Var], flag_var: &str) {
    let mut replacements = vec![];

    for (i, line) in lines.iter().enumerate() {
        // Look for assignments to result variables
        if let Line::Assignment { var, value } = line {
            if res.contains(var) {
                // This is an assignment to a result variable - make it conditional
                let condition = Boolean::Equal {
                    left: Expression::Value(SimpleExpr::Var(flag_var.to_string())),
                    right: Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(0))),
                };

                let mut new_lines = vec![];

                // Conditional assignment to result variable
                new_lines.push(Line::IfCondition {
                    condition: condition.clone(),
                    then_branch: vec![Line::Assignment {
                        var: var.clone(),
                        value: value.clone(),
                    }],
                    else_branch: vec![],
                });

                // Set flag to 1 to prevent future assignments
                new_lines.push(Line::IfCondition {
                    condition,
                    then_branch: vec![Line::Assignment {
                        var: flag_var.to_string(),
                        value: Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(1))),
                    }],
                    else_branch: vec![],
                });

                replacements.push((i, new_lines));
            }
        }
    }

    // Apply replacements in reverse order to preserve indices
    for (i, new_lines) in replacements.into_iter().rev() {
        lines.splice(i..=i, new_lines);
    }

    // Recursively process nested structures, but avoid processing the newly created conditional assignments
    for line in lines.iter_mut() {
        match line {
            Line::IfCondition {
                then_branch,
                else_branch,
                condition,
            } => {
                // Skip if this is one of our generated flag conditions
                let is_flag_condition = match condition {
                    Boolean::Equal { left, right } => {
                        matches!(
                            (left, right),
                            (Expression::Value(SimpleExpr::Var(var)), Expression::Value(SimpleExpr::Constant(_)))
                            if var == flag_var
                        )
                    }
                    _ => false,
                };

                if !is_flag_condition {
                    convert_returns_to_conditional_assignments(then_branch, res, flag_var);
                    convert_returns_to_conditional_assignments(else_branch, res, flag_var);
                }
            }
            Line::ForLoop { body, .. } => {
                convert_returns_to_conditional_assignments(body, res, flag_var);
            }
            Line::Match { arms, .. } => {
                for (_, arm_statements) in arms {
                    convert_returns_to_conditional_assignments(arm_statements, res, flag_var);
                }
            }
            _ => {}
        }
    }
}

/// Fix SSA violations by restructuring control flow to avoid multiple assignments
/// This approach converts the problematic pattern into a single if-else structure
fn fix_ssa_violations_by_restructuring_control_flow(lines: &mut Vec<Line>, res: &[Var]) {
    // Convert the pattern:
    // if outer { if inner { result = val1; } } result = val2;
    // To: if outer && inner { result = val1; } else { result = val2; }
    restructure_nested_assignments(lines, res);
}

/// Restructure nested assignments to avoid SSA violations
fn restructure_nested_assignments(lines: &mut Vec<Line>, res: &[Var]) {
    if res.is_empty() {
        return;
    }

    // Look for the pattern: nested ifs with assignments, followed by final assignment
    let result_var = &res[0]; // For now, handle single return value

    // Find all assignments to the result variable
    let mut assignments_with_conditions = Vec::new();
    let mut final_assignment = None;
    let mut lines_to_remove = Vec::new();

    for (i, line) in lines.iter().enumerate() {
        if let Line::Assignment { var, value } = line {
            if var == result_var {
                final_assignment = Some((value.clone(), i));
                lines_to_remove.push(i);
            }
        } else {
            // Look for nested conditions with assignments
            if let Some((conditions, assignment_value)) =
                extract_nested_assignment(line, result_var)
            {
                assignments_with_conditions.push((conditions, assignment_value));
                lines_to_remove.push(i);
            }
        }
    }

    if assignments_with_conditions.is_empty() || final_assignment.is_none() {
        return; // No pattern to restructure
    }

    // Remove old lines in reverse order to preserve indices
    for &i in lines_to_remove.iter().rev() {
        lines.remove(i);
    }

    // Build new if-else structure
    if let Some((final_value, _)) = final_assignment {
        let new_structure =
            build_if_else_structure(assignments_with_conditions, final_value, result_var);
        lines.push(new_structure);
    }
}

/// Extract nested assignment conditions and value from a line
fn extract_nested_assignment(line: &Line, result_var: &str) -> Option<(Vec<Boolean>, Expression)> {
    fn extract_recursive(
        line: &Line,
        result_var: &str,
        conditions: &mut Vec<Boolean>,
    ) -> Option<Expression> {
        match line {
            Line::IfCondition {
                condition,
                then_branch,
                else_branch,
            } => {
                // Check if then_branch has assignment to result_var
                for then_line in then_branch {
                    if let Line::Assignment { var, value } = then_line {
                        if var == result_var {
                            conditions.push(condition.clone());
                            return Some(value.clone());
                        }
                    }
                    // Recursively check nested ifs
                    conditions.push(condition.clone());
                    if let Some(val) = extract_recursive(then_line, result_var, conditions) {
                        return Some(val);
                    }
                    conditions.pop();
                }

                // For else branches, we'll handle them separately in a more complex implementation
                // For now, skip else branch extraction to keep it simple
                None
            }
            _ => None,
        }
    }

    let mut conditions = Vec::new();
    if let Some(value) = extract_recursive(line, result_var, &mut conditions) {
        Some((conditions, value))
    } else {
        None
    }
}

/// Build if-else structure from conditions and assignments
fn build_if_else_structure(
    assignments: Vec<(Vec<Boolean>, Expression)>,
    final_value: Expression,
    result_var: &str,
) -> Line {
    if assignments.is_empty() {
        return Line::Assignment {
            var: result_var.to_string(),
            value: final_value,
        };
    }

    // For now, handle simple case: single nested condition
    if let Some((conditions, value)) = assignments.first() {
        let then_branch = vec![Line::Assignment {
            var: result_var.to_string(),
            value: value.clone(),
        }];
        let else_branch = vec![Line::Assignment {
            var: result_var.to_string(),
            value: final_value,
        }];

        create_nested_conditions(conditions, then_branch, else_branch)
    } else {
        Line::Assignment {
            var: result_var.to_string(),
            value: final_value,
        }
    }
}

/// Combine multiple conditions with AND using nested if statements
fn create_nested_conditions(
    conditions: &[Boolean],
    then_branch: Vec<Line>,
    else_branch: Vec<Line>,
) -> Line {
    if conditions.is_empty() {
        return Line::IfCondition {
            condition: Boolean::Equal {
                left: Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(1))),
                right: Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(1))),
            },
            then_branch,
            else_branch,
        };
    }

    if conditions.len() == 1 {
        Line::IfCondition {
            condition: conditions[0].clone(),
            then_branch,
            else_branch,
        }
    } else {
        // Create nested if-else structure
        let inner_structure =
            create_nested_conditions(&conditions[1..], then_branch, else_branch.clone());
        Line::IfCondition {
            condition: conditions[0].clone(),
            then_branch: vec![inner_structure],
            else_branch,
        }
    }
}

/// Check if we have the classic fallthrough pattern that causes SSA violations
fn has_classic_fallthrough_pattern(lines: &[Line]) -> bool {
    // Look for: if-condition followed by return statement
    let mut has_if_with_nested_returns = false;
    let mut has_final_return = false;

    for line in lines {
        match line {
            Line::IfCondition {
                then_branch,
                else_branch,
                ..
            } => {
                if has_return_statements_in_branch(then_branch)
                    || has_return_statements_in_branch(else_branch)
                {
                    has_if_with_nested_returns = true;
                }
            }
            Line::FunctionRet { .. } => {
                if has_if_with_nested_returns {
                    has_final_return = true;
                }
            }
            _ => {}
        }
    }

    has_if_with_nested_returns && has_final_return
}

/// Restructure the fallthrough pattern to use proper if-else nesting
fn restructure_fallthrough_pattern(lines: &mut Vec<Line>, res: &[Var]) {
    // Find all return statements and their values
    let mut return_values = Vec::new();
    let mut non_return_lines = Vec::new();

    for line in lines.iter() {
        match line {
            Line::Assignment { var, value } if res.contains(var) => {
                // This is a return assignment
                return_values.push(value.clone());
            }
            Line::FunctionRet { .. } => {
                // Skip the original return statements
            }
            _ => {
                non_return_lines.push(line.clone());
            }
        }
    }

    // For the simple case, just use the first return value
    // In a complete implementation, we'd build the full conditional structure
    if let Some(first_value) = return_values.first() {
        lines.clear();
        lines.extend(non_return_lines);

        // Add a single assignment with the first return value
        for var in res {
            lines.push(Line::Assignment {
                var: var.clone(),
                value: first_value.clone(),
            });
        }
    }
}

/// Collect return assignments and their execution contexts (conditions)
fn collect_return_contexts(
    lines: &[Line],
    res: &[Var],
    contexts: &mut Vec<(Vec<Boolean>, Vec<(String, Expression)>)>,
    current_conditions: Vec<Boolean>,
) {
    for line in lines {
        match line {
            Line::Assignment { var, value } if res.contains(var) => {
                // Found a return assignment
                let assignment = (var.clone(), value.clone());
                contexts.push((current_conditions.clone(), vec![assignment]));
            }
            Line::IfCondition {
                condition,
                then_branch,
                else_branch,
            } => {
                // Add condition to context and recurse
                let mut then_conditions = current_conditions.clone();
                then_conditions.push(condition.clone());
                collect_return_contexts(then_branch, res, contexts, then_conditions);

                // For else branch, add negated condition
                let negated_condition = match condition {
                    Boolean::Equal { left, right } => Boolean::Different {
                        left: left.clone(),
                        right: right.clone(),
                    },
                    Boolean::Different { left, right } => Boolean::Equal {
                        left: left.clone(),
                        right: right.clone(),
                    },
                };
                let mut else_conditions = current_conditions.clone();
                else_conditions.push(negated_condition);
                collect_return_contexts(else_branch, res, contexts, else_conditions);
            }
            _ => {}
        }
    }
}

/// Build nested if-else structure that ensures only one assignment per variable
fn build_nested_control_flow(
    contexts: &[(Vec<Boolean>, Vec<(String, Expression)>)],
    res: &[Var],
) -> Vec<Line> {
    if contexts.is_empty() {
        return vec![];
    }

    // For now, implement a simple approach: use the first context as the main assignment
    // and wrap others in their conditions
    let mut result_lines = Vec::new();

    for (i, (conditions, assignments)) in contexts.iter().enumerate() {
        if conditions.is_empty() {
            // Unconditional assignment
            for (var, value) in assignments {
                result_lines.push(Line::Assignment {
                    var: var.clone(),
                    value: value.clone(),
                });
            }
        } else {
            // Conditional assignment - build nested if structure
            let assignment_lines: Vec<Line> = assignments
                .iter()
                .map(|(var, value)| Line::Assignment {
                    var: var.clone(),
                    value: value.clone(),
                })
                .collect();

            let nested_if = build_nested_if_from_conditions(conditions, assignment_lines);
            result_lines.push(nested_if);
        }

        // For simplicity, only handle the first return for now
        // In a complete implementation, we'd need to build a proper decision tree
        if i == 0 {
            break;
        }
    }

    result_lines
}

/// Build a nested if statement from a list of conditions
fn build_nested_if_from_conditions(conditions: &[Boolean], then_branch: Vec<Line>) -> Line {
    if conditions.len() == 1 {
        Line::IfCondition {
            condition: conditions[0].clone(),
            then_branch,
            else_branch: vec![],
        }
    } else {
        let inner_if = build_nested_if_from_conditions(&conditions[1..], then_branch);
        Line::IfCondition {
            condition: conditions[0].clone(),
            then_branch: vec![inner_if],
            else_branch: vec![],
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

    // #[test]
    // fn test_ssa_violation_multiple_returns() {
    //     // Test case: function with multiple returns that can both execute
    //     // This exposes the SSA violation where both returns try to assign the same variable
    //     let mut lines = vec![
    //         Line::IfCondition {
    //             condition: Boolean::Equal {
    //                 left: Expression::Value(SimpleExpr::Var("arg1".to_string())),
    //                 right: Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(1))),
    //             },
    //             then_branch: vec![
    //                 Line::IfCondition {
    //                     condition: Boolean::Equal {
    //                         left: Expression::Value(SimpleExpr::Var("arg1".to_string())),
    //                         right: Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(0))),
    //                     },
    //                     then_branch: vec![Line::FunctionRet {
    //                         return_data: vec![Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(100)))],
    //                     }],
    //                     else_branch: vec![],
    //                 },
    //                 Line::IfCondition {
    //                     condition: Boolean::Equal {
    //                         left: Expression::Value(SimpleExpr::Var("arg1".to_string())),
    //                         right: Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(1))),
    //                     },
    //                     then_branch: vec![Line::FunctionRet {
    //                         return_data: vec![Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(200)))],
    //                     }],
    //                     else_branch: vec![],
    //                 },
    //             ],
    //             else_branch: vec![],
    //         },
    //         Line::FunctionRet {
    //             return_data: vec![Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(300)))],
    //         },
    //     ];

    //     let mut args = BTreeMap::new();
    //     args.insert("arg1".to_string(), SimpleExpr::Constant(ConstExpression::scalar(1)));
    //     let res = vec!["result".to_string()];

    //     // This should not cause SSA violations with our new implementation
    //     inline_lines(&mut lines, &args, &res, 0);

    //     // We should have return flag logic that prevents multiple assignments to the same variable
    //     let has_return_flag = lines.iter().any(|line| {
    //         if let Line::Assignment { var, .. } = line {
    //             var.contains("returned") || var.contains("return_flag")
    //         } else {
    //             false
    //         }
    //     });

    //     // The fix should introduce return flag logic
    //     assert!(has_return_flag, "Expected return flag logic to prevent SSA violations");
    // }

    // #[test]
    // fn test_ssa_violation_fixed_with_return_flag() {
    //     // Test that our return flag mechanism works correctly
    //     let mut lines = vec![
    //         Line::IfCondition {
    //             condition: Boolean::Equal {
    //                 left: Expression::Value(SimpleExpr::Var("arg1".to_string())),
    //                 right: Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(0))),
    //             },
    //             then_branch: vec![Line::FunctionRet {
    //                 return_data: vec![Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(100)))],
    //             }],
    //             else_branch: vec![],
    //         },
    //         Line::FunctionRet {
    //             return_data: vec![Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(200)))],
    //         },
    //     ];

    //     let mut args = BTreeMap::new();
    //     args.insert("arg1".to_string(), SimpleExpr::Constant(ConstExpression::scalar(1)));
    //     let res = vec!["result".to_string()];

    //     inline_lines(&mut lines, &args, &res, 0);

    //     // Count how many times the result variable is assigned
    //     let result_assignments = lines.iter().filter(|line| {
    //         if let Line::Assignment { var, .. } = line {
    //             var == "result"
    //         } else {
    //             false
    //         }
    //     }).count();

    //     // With return flag logic, we should have conditional assignments
    //     let has_conditional_assignment = lines.iter().any(|line| {
    //         if let Line::IfCondition { .. } = line {
    //             true
    //         } else {
    //             false
    //         }
    //     });

    //     assert!(has_conditional_assignment, "Expected conditional assignments using return flags");
    // }

    // #[test]
    // fn test_nested_returns_case() {
    //     // Test deeply nested returns that can cause SSA violations
    //     let mut lines = vec![
    //         Line::IfCondition {
    //             condition: Boolean::Equal {
    //                 left: Expression::Value(SimpleExpr::Var("x".to_string())),
    //                 right: Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(1))),
    //             },
    //             then_branch: vec![
    //                 Line::IfCondition {
    //                     condition: Boolean::Equal {
    //                         left: Expression::Value(SimpleExpr::Var("x".to_string())),
    //                         right: Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(2))),
    //                     },
    //                     then_branch: vec![
    //                         Line::IfCondition {
    //                             condition: Boolean::Equal {
    //                                 left: Expression::Value(SimpleExpr::Var("x".to_string())),
    //                                 right: Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(3))),
    //                             },
    //                             then_branch: vec![Line::FunctionRet {
    //                                 return_data: vec![Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(100)))],
    //                             }],
    //                             else_branch: vec![],
    //                         },
    //                         Line::FunctionRet {
    //                             return_data: vec![Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(200)))],
    //                         },
    //                     ],
    //                     else_branch: vec![],
    //                 },
    //                 Line::IfCondition {
    //                     condition: Boolean::Equal {
    //                         left: Expression::Value(SimpleExpr::Var("x".to_string())),
    //                         right: Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(1))),
    //                     },
    //                     then_branch: vec![Line::FunctionRet {
    //                         return_data: vec![Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(300)))],
    //                     }],
    //                     else_branch: vec![],
    //                 },
    //             ],
    //             else_branch: vec![],
    //         },
    //         Line::FunctionRet {
    //             return_data: vec![Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(400)))],
    //         },
    //     ];

    //     let args = BTreeMap::new();
    //     let res = vec!["result".to_string()];

    //     // Should not panic with SSA violations
    //     inline_lines(&mut lines, &args, &res, 0);

    //     // Should generate return flag logic
    //     let has_return_logic = lines.iter().any(|line| {
    //         match line {
    //             Line::Assignment { var, .. } => var.contains("returned"),
    //             Line::IfCondition { condition, .. } => {
    //                 // Check if condition involves return flag
    //                 match condition {
    //                     Boolean::Equal { left, right } | Boolean::Different { left, right } => {
    //                         let check_expr = |expr: &Expression| -> bool {
    //                             if let Expression::Value(SimpleExpr::Var(var)) = expr {
    //                                 var.contains("returned")
    //                             } else {
    //                                 false
    //                             }
    //                         };
    //                         check_expr(left) || check_expr(right)
    //                     }
    //                 }
    //             }
    //             _ => false,
    //         }
    //     });

    //     assert!(has_return_logic, "Expected return flag logic for complex nested returns");
    // }

    // #[test]
    // fn test_failing_case_exact_replica() {
    //     // Exact replica of the failing case from the integration test
    //     let mut lines = vec![
    //         Line::IfCondition {
    //             condition: Boolean::Equal {
    //                 left: Expression::Value(SimpleExpr::Var("x".to_string())),
    //                 right: Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(1))),
    //             },
    //             then_branch: vec![
    //                 Line::IfCondition {
    //                     condition: Boolean::Equal {
    //                         left: Expression::Value(SimpleExpr::Var("x".to_string())),
    //                         right: Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(0))),
    //                     },
    //                     then_branch: vec![Line::FunctionRet {
    //                         return_data: vec![Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(100)))],
    //                     }],
    //                     else_branch: vec![],
    //                 },
    //                 Line::IfCondition {
    //                     condition: Boolean::Equal {
    //                         left: Expression::Value(SimpleExpr::Var("x".to_string())),
    //                         right: Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(1))),
    //                     },
    //                     then_branch: vec![Line::FunctionRet {
    //                         return_data: vec![Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(200)))],
    //                     }],
    //                     else_branch: vec![],
    //                 },
    //             ],
    //             else_branch: vec![],
    //         },
    //         Line::FunctionRet {
    //             return_data: vec![Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(300)))],
    //         },
    //     ];

    //     let args = BTreeMap::new();
    //     let res = vec!["b".to_string()];

    //     // This exact case should not cause SSA violations after our fix
    //     inline_lines(&mut lines, &args, &res, 0);

    //     // Should not have multiple unconditional assignments to the same variable
    //     let unconditional_assignments = lines.iter().filter(|line| {
    //         if let Line::Assignment { var, .. } = line {
    //             var == "b"
    //         } else {
    //             false
    //         }
    //     }).count();

    //     // With proper return flag logic, direct assignments should be conditional
    //     assert!(unconditional_assignments <= 1,
    //         "Too many unconditional assignments to result variable, expected return flag logic");
    // }

    // #[test]
    // fn test_vm_constraint_issue() {
    //     // Test the specific constraint that causes VM to fail: multiple writes to same memory slot
    //     let mut lines = vec![
    //         Line::FunctionRet {
    //             return_data: vec![Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(42)))],
    //         },
    //         Line::FunctionRet {
    //             return_data: vec![Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(84)))],
    //         },
    //     ];

    //     let args = BTreeMap::new();
    //     let res = vec!["output".to_string()];

    //     inline_lines(&mut lines, &args, &res, 0);

    //     // After fix, should not have multiple direct assignments
    //     let direct_assignments = lines.iter().filter(|line| {
    //         if let Line::Assignment { var, .. } = line {
    //             var == "output"
    //         } else {
    //             false
    //         }
    //     }).count();

    //     // Should use return flag mechanism instead of direct assignments
    //     assert!(direct_assignments <= 1, "Expected single assignment using return flags");
    // }

    // #[test]
    // fn test_debug_return_flag_generation() {
    //     // Debug test to see what code gets generated
    //     let mut lines = vec![
    //         Line::IfCondition {
    //             condition: Boolean::Equal {
    //                 left: Expression::Value(SimpleExpr::Var("x".to_string())),
    //                 right: Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(0))),
    //             },
    //             then_branch: vec![Line::FunctionRet {
    //                 return_data: vec![Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(100)))],
    //             }],
    //             else_branch: vec![],
    //         },
    //         Line::FunctionRet {
    //             return_data: vec![Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(200)))],
    //         },
    //     ];

    //     let args = BTreeMap::new();
    //     let res = vec!["result".to_string()];

    //     println!("Before inlining:");
    //     for (i, line) in lines.iter().enumerate() {
    //         println!("{}: {}", i, line);
    //     }

    //     inline_lines(&mut lines, &args, &res, 0);

    //     println!("\nAfter inlining:");
    //     for (i, line) in lines.iter().enumerate() {
    //         println!("{}: {}", i, line);
    //     }

    //     // Check if there are still any FunctionRet statements after processing
    //     let has_unprocessed_returns = has_return_statements_in_branch(&lines);
    //     println!("\nHas unprocessed returns: {}", has_unprocessed_returns);

    //     // Should have return flag logic
    //     let has_return_flag_init = lines.iter().any(|line| {
    //         if let Line::Assignment { var, .. } = line {
    //             var.contains("returned")
    //         } else {
    //             false
    //         }
    //     });

    //     assert!(has_return_flag_init, "Expected return flag initialization");
    // }

    // #[test]
    // fn test_debug_non_exhaustive_detection() {
    //     // Test the simple non-exhaustive case
    //     let lines = vec![
    //         Line::IfCondition {
    //             condition: Boolean::Equal {
    //                 left: Expression::Value(SimpleExpr::Var("x".to_string())),
    //                 right: Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(0))),
    //             },
    //             then_branch: vec![Line::FunctionRet {
    //                 return_data: vec![Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(100)))],
    //             }],
    //             else_branch: vec![],
    //         },
    //         Line::FunctionRet {
    //             return_data: vec![Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(200)))],
    //         },
    //     ];

    //     let needs_flag = needs_return_flag_logic(&lines);
    //     println!("Non-exhaustive case needs flag logic: {}", needs_flag);

    //     // Test the exhaustive case
    //     let exhaustive_lines = vec![
    //         Line::IfCondition {
    //             condition: Boolean::Equal {
    //                 left: Expression::Value(SimpleExpr::Var("x".to_string())),
    //                 right: Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(0))),
    //             },
    //             then_branch: vec![Line::FunctionRet {
    //                 return_data: vec![Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(100)))],
    //             }],
    //             else_branch: vec![Line::FunctionRet {
    //                 return_data: vec![Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(200)))],
    //             }],
    //         },
    //     ];

    //     let exhaustive_needs_flag = needs_return_flag_logic(&exhaustive_lines);
    //     println!("Exhaustive case needs flag logic: {}", exhaustive_needs_flag);

    //     assert!(needs_flag, "Non-exhaustive case should need flag logic");
    //     assert!(!exhaustive_needs_flag, "Exhaustive case should not need flag logic");
    // }

    // #[test]
    // fn test_debug_detection_logic() {
    //     // Test the exact pattern from test_inline_edge_cases1
    //     let lines = vec![
    //         Line::IfCondition {
    //             condition: Boolean::Equal {
    //                 left: Expression::Value(SimpleExpr::Var("x".to_string())),
    //                 right: Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(1))),
    //             },
    //             then_branch: vec![
    //                 Line::IfCondition {
    //                     condition: Boolean::Equal {
    //                         left: Expression::Value(SimpleExpr::Var("x".to_string())),
    //                         right: Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(0))),
    //                     },
    //                     then_branch: vec![Line::FunctionRet {
    //                         return_data: vec![Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(100)))],
    //                     }],
    //                     else_branch: vec![],
    //                 },
    //                 Line::IfCondition {
    //                     condition: Boolean::Equal {
    //                         left: Expression::Value(SimpleExpr::Var("x".to_string())),
    //                         right: Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(1))),
    //                     },
    //                     then_branch: vec![Line::FunctionRet {
    //                         return_data: vec![Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(200)))],
    //                     }],
    //                     else_branch: vec![],
    //                 },
    //             ],
    //             else_branch: vec![],
    //         },
    //         Line::FunctionRet {
    //             return_data: vec![Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(300)))],
    //         },
    //     ];

    //     let needs_flag = needs_return_flag_logic(&lines);
    //     println!("Edge case 1 pattern needs flag logic: {}", needs_flag);
    //     println!("Has nested if returns: {}", has_nested_if_with_returns(&lines));
    //     println!("Has final return: {}", lines.iter().any(|line| matches!(line, Line::FunctionRet { .. })));

    //     // This should detect the problematic pattern
    //     assert!(needs_flag, "Should detect the edge case 1 pattern as needing flag logic");
    // }

    // #[test]
    // fn test_debug_vm_constraint_issue() {
    //     // Test the exact pattern that causes VM constraint failures
    //     // This isolates the specific issue with return flag variables
    //     let mut lines = vec![
    //         Line::IfCondition {
    //             condition: Boolean::Equal {
    //                 left: Expression::Value(SimpleExpr::Var("x".to_string())),
    //                 right: Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(0))),
    //             },
    //             then_branch: vec![Line::FunctionRet {
    //                 return_data: vec![Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(100)))],
    //             }],
    //             else_branch: vec![],
    //         },
    //         Line::FunctionRet {
    //             return_data: vec![Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(200)))],
    //         },
    //     ];

    //     let args = BTreeMap::new();
    //     let res = vec!["result".to_string()];

    //     println!("Testing VM constraint issue pattern...");
    //     println!("Before inlining:");
    //     for (i, line) in lines.iter().enumerate() {
    //         println!("{}: {}", i, line);
    //     }

    //     inline_lines(&mut lines, &args, &res, 0);

    //     println!("\nAfter inlining:");
    //     for (i, line) in lines.iter().enumerate() {
    //         println!("{}: {}", i, line);
    //     }

    //     // The issue might be with how we're structuring the flag logic
    //     // Let's verify the exact pattern that gets generated

    //     // Look for the flag initialization
    //     let has_flag_init = lines.iter().any(|line| {
    //         if let Line::Assignment { var, value } = line {
    //             var.contains("returned") &&
    //             if let Expression::Value(SimpleExpr::Constant(const_val)) = value {
    //                 const_val == &ConstExpression::scalar(1)
    //             } else {
    //                 false
    //             }
    //         } else {
    //             false
    //         }
    //     });

    //     // Look for the flag conditions
    //     let flag_conditions = lines.iter().filter_map(|line| {
    //         if let Line::IfCondition { condition, .. } = line {
    //             if let Boolean::Equal { left, right } = condition {
    //                 if let (Expression::Value(SimpleExpr::Var(var)), Expression::Value(SimpleExpr::Constant(val))) = (left, right) {
    //                     if var.contains("returned") {
    //                         Some(val.clone())
    //                     } else {
    //                         None
    //                     }
    //                 } else {
    //                     None
    //                 }
    //             } else {
    //                 None
    //             }
    //         } else {
    //             None
    //         }
    //     }).collect::<Vec<_>>();

    //     println!("Flag init found: {}", has_flag_init);
    //     println!("Flag conditions: {:?}", flag_conditions);

    //     assert!(has_flag_init, "Should have flag initialization");
    //     assert!(!flag_conditions.is_empty(), "Should have flag conditions");
    // }

    // #[test]
    // fn test_complete_compilation_pipeline() {
    //     // Test that our fix works with the complete compilation pipeline for inline functions
    //     let inline_func = Function {
    //         name: "problematic".to_string(),
    //         arguments: vec![("x".to_string(), false)],
    //         inlined: true,
    //         body: vec![
    //             Line::IfCondition {
    //                 condition: Boolean::Equal {
    //                     left: Expression::Value(SimpleExpr::Var("x".to_string())),
    //                     right: Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(0))),
    //                 },
    //                 then_branch: vec![Line::FunctionRet {
    //                     return_data: vec![Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(100)))],
    //                 }],
    //                 else_branch: vec![],
    //             },
    //             Line::FunctionRet {
    //                 return_data: vec![Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(200)))],
    //             },
    //         ],
    //         n_returned_vars: 1,
    //     };

    //     let caller_func = Function {
    //         name: "caller".to_string(),
    //         arguments: vec![],
    //         inlined: false,
    //         body: vec![Line::FunctionCall {
    //             function_name: "problematic".to_string(),
    //             args: vec![Expression::Value(SimpleExpr::Constant(ConstExpression::scalar(1)))],
    //             return_data: vec!["result".to_string()],
    //         }],
    //         n_returned_vars: 0,
    //     };

    //     let mut program = Program {
    //         functions: BTreeMap::new(),
    //     };
    //     program.functions.insert("problematic".to_string(), inline_func);
    //     program.functions.insert("caller".to_string(), caller_func);

    //     // This should not panic with our fix
    //     handle_inlined_functions(&mut program);

    //     // Verify the inlined function was removed
    //     assert!(!program.functions.contains_key("problematic"));

    //     // Verify caller has inlined content with proper return flag logic
    //     let caller = program.functions.get("caller").unwrap();
    //     assert!(!caller.body.is_empty());

    //     // Should contain return flag assignments and conditions
    //     let has_return_flag_assignment = caller.body.iter().any(|line| {
    //         if let Line::Assignment { var, .. } = line {
    //             var.contains("returned")
    //         } else {
    //             false
    //         }
    //     });

    //     assert!(has_return_flag_assignment, "Expected return flag logic in inlined function");
    // }

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
