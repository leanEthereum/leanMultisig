use super::{
    types::{
        ArrayAccessType, ArrayManager, ConstMalloc, Counters, SimpleFunction, SimpleLine,
        VarOrConstMallocAccess,
    },
    utilities::find_variable_usage,
};
use crate::{
    ir::HighLevelOperation,
    lang::{Boolean, ConstExpression, Expression, Line, SimpleExpr, Var},
};
use std::collections::BTreeMap;
use utils::ToUsize;

/// Simplify a sequence of lines into SimpleLine format.
pub fn simplify_lines(
    lines: &[Line],
    counters: &mut Counters,
    new_functions: &mut BTreeMap<String, SimpleFunction>,
    in_a_loop: bool,
    array_manager: &mut ArrayManager,
    const_malloc: &mut ConstMalloc,
) -> Vec<SimpleLine> {
    let mut res = Vec::new();
    for line in lines {
        match line {
            Line::Match { value, arms } => {
                let simple_value =
                    simplify_expr(value, &mut res, counters, array_manager, const_malloc);
                let mut simple_arms = vec![];
                for (i, (pattern, statements)) in arms.iter().enumerate() {
                    assert_eq!(
                        *pattern, i,
                        "match patterns should be consecutive, starting from 0"
                    );
                    simple_arms.push(simplify_lines(
                        statements,
                        counters,
                        new_functions,
                        in_a_loop,
                        array_manager,
                        const_malloc,
                    ));
                }
                res.push(SimpleLine::Match {
                    value: simple_value,
                    arms: simple_arms,
                });
            }
            Line::Assignment { var, value } => match value {
                Expression::Value(value) => {
                    res.push(SimpleLine::Assignment {
                        var: var.clone().into(),
                        operation: HighLevelOperation::Add,
                        arg0: value.clone(),
                        arg1: SimpleExpr::zero(),
                    });
                }
                Expression::ArrayAccess { array, index } => {
                    handle_array_assignment(
                        counters,
                        &mut res,
                        array.clone(),
                        index,
                        ArrayAccessType::VarIsAssigned(var.clone()),
                        array_manager,
                        const_malloc,
                    );
                }
                Expression::Binary {
                    left,
                    operation,
                    right,
                } => {
                    let left = simplify_expr(left, &mut res, counters, array_manager, const_malloc);
                    let right =
                        simplify_expr(right, &mut res, counters, array_manager, const_malloc);
                    res.push(SimpleLine::Assignment {
                        var: var.clone().into(),
                        operation: *operation,
                        arg0: left,
                        arg1: right,
                    });
                }
                Expression::Log2Ceil { .. } => unreachable!(),
            },
            Line::ArrayAssign {
                array,
                index,
                value,
            } => {
                handle_array_assignment(
                    counters,
                    &mut res,
                    array.clone(),
                    index,
                    ArrayAccessType::ArrayIsAssigned(value.clone()),
                    array_manager,
                    const_malloc,
                );
            }
            Line::Assert(boolean) => match boolean {
                Boolean::Different { left, right } => {
                    let left = simplify_expr(left, &mut res, counters, array_manager, const_malloc);
                    let right =
                        simplify_expr(right, &mut res, counters, array_manager, const_malloc);
                    let diff_var = format!("@aux_var_{}", counters.aux_vars);
                    counters.aux_vars += 1;
                    res.push(SimpleLine::Assignment {
                        var: diff_var.clone().into(),
                        operation: HighLevelOperation::Sub,
                        arg0: left,
                        arg1: right,
                    });
                    res.push(SimpleLine::IfNotZero {
                        condition: diff_var.into(),
                        then_branch: vec![],
                        else_branch: vec![SimpleLine::Panic],
                    });
                }
                Boolean::Equal { left, right } => {
                    let left = simplify_expr(left, &mut res, counters, array_manager, const_malloc);
                    let right =
                        simplify_expr(right, &mut res, counters, array_manager, const_malloc);
                    let (var, other) = if let Ok(left) = left.clone().try_into() {
                        (left, right)
                    } else if let Ok(right) = right.clone().try_into() {
                        (right, left)
                    } else {
                        unreachable!("Weird: {:?}, {:?}", left, right)
                    };
                    res.push(SimpleLine::Assignment {
                        var,
                        operation: HighLevelOperation::Add,
                        arg0: other,
                        arg1: SimpleExpr::zero(),
                    });
                }
            },
            Line::IfCondition {
                condition,
                then_branch,
                else_branch,
            } => {
                handle_if_condition(
                    condition,
                    then_branch,
                    else_branch,
                    &mut res,
                    counters,
                    new_functions,
                    in_a_loop,
                    array_manager,
                    const_malloc,
                );
            }
            Line::ForLoop {
                iterator,
                start,
                end,
                body,
                rev,
                unroll,
            } => {
                handle_for_loop(
                    iterator,
                    start,
                    end,
                    body,
                    *rev,
                    *unroll,
                    &mut res,
                    counters,
                    new_functions,
                    in_a_loop,
                    array_manager,
                    const_malloc,
                );
            }
            Line::FunctionCall {
                function_name,
                args,
                return_data,
            } => {
                let simplified_args = args
                    .iter()
                    .map(|arg| simplify_expr(arg, &mut res, counters, array_manager, const_malloc))
                    .collect::<Vec<_>>();
                res.push(SimpleLine::FunctionCall {
                    function_name: function_name.clone(),
                    args: simplified_args,
                    return_data: return_data.clone(),
                });
            }
            Line::FunctionRet { return_data } => {
                assert!(
                    !in_a_loop,
                    "Function return inside a loop is not currently supported"
                );
                let simplified_return_data = return_data
                    .iter()
                    .map(|ret| simplify_expr(ret, &mut res, counters, array_manager, const_malloc))
                    .collect::<Vec<_>>();
                res.push(SimpleLine::FunctionRet {
                    return_data: simplified_return_data,
                });
            }
            Line::Precompile { precompile, args } => {
                let simplified_args = args
                    .iter()
                    .map(|arg| simplify_expr(arg, &mut res, counters, array_manager, const_malloc))
                    .collect::<Vec<_>>();
                res.push(SimpleLine::Precompile {
                    precompile: precompile.clone(),
                    args: simplified_args,
                });
            }
            Line::Print { line_info, content } => {
                let simplified_content = content
                    .iter()
                    .map(|var| simplify_expr(var, &mut res, counters, array_manager, const_malloc))
                    .collect::<Vec<_>>();
                res.push(SimpleLine::Print {
                    line_info: line_info.clone(),
                    content: simplified_content,
                });
            }
            Line::Break => {
                assert!(in_a_loop, "Break statement outside of a loop");
                res.push(SimpleLine::FunctionRet {
                    return_data: vec![],
                });
            }
            Line::MAlloc {
                var,
                size,
                vectorized,
                vectorized_len,
            } => {
                handle_malloc(
                    var,
                    size,
                    *vectorized,
                    vectorized_len,
                    &mut res,
                    counters,
                    array_manager,
                    const_malloc,
                );
            }
            Line::DecomposeBits { var, to_decompose } => {
                assert!(!const_malloc.forbidden_vars.contains(var), "TODO");
                let simplified_to_decompose = to_decompose
                    .iter()
                    .map(|expr| {
                        simplify_expr(expr, &mut res, counters, array_manager, const_malloc)
                    })
                    .collect::<Vec<_>>();
                let label = const_malloc.counter;
                const_malloc.counter += 1;
                const_malloc.map.insert(var.clone(), label);
                res.push(SimpleLine::DecomposeBits {
                    var: var.clone(),
                    to_decompose: simplified_to_decompose,
                    label,
                });
            }
            Line::CounterHint { var } => {
                res.push(SimpleLine::CounterHint { var: var.clone() });
            }
            Line::Panic => {
                res.push(SimpleLine::Panic);
            }
            Line::LocationReport { location } => {
                res.push(SimpleLine::LocationReport {
                    location: *location,
                });
            }
        }
    }

    res
}

/// Simplify an expression into SimpleExpr format.
pub fn simplify_expr(
    expr: &Expression,
    lines: &mut Vec<SimpleLine>,
    counters: &mut Counters,
    array_manager: &mut ArrayManager,
    const_malloc: &ConstMalloc,
) -> SimpleExpr {
    match expr {
        Expression::Value(value) => value.simplify_if_const(),
        Expression::ArrayAccess { array, index } => {
            if let SimpleExpr::Var(array_var) = array
                && let Some(label) = const_malloc.map.get(array_var)
                && let Ok(mut offset) = ConstExpression::try_from(*index.clone())
            {
                offset = offset.try_naive_simplification();
                return SimpleExpr::ConstMallocAccess {
                    malloc_label: *label,
                    offset,
                };
            }

            let aux_arr = array_manager.get_aux_var(array, index); // auxiliary var to store m[array + index]

            if !array_manager.valid.insert(aux_arr.clone()) {
                return SimpleExpr::Var(aux_arr);
            }

            handle_array_assignment(
                counters,
                lines,
                array.clone(),
                index,
                ArrayAccessType::VarIsAssigned(aux_arr.clone()),
                array_manager,
                const_malloc,
            );
            SimpleExpr::Var(aux_arr)
        }
        Expression::Binary {
            left,
            operation,
            right,
        } => {
            let left_var = simplify_expr(left, lines, counters, array_manager, const_malloc);
            let right_var = simplify_expr(right, lines, counters, array_manager, const_malloc);

            if let (SimpleExpr::Constant(left_cst), SimpleExpr::Constant(right_cst)) =
                (&left_var, &right_var)
            {
                return SimpleExpr::Constant(ConstExpression::Binary {
                    left: Box::new(left_cst.clone()),
                    operation: *operation,
                    right: Box::new(right_cst.clone()),
                });
            }

            let aux_var = format!("@aux_var_{}", counters.aux_vars);
            counters.aux_vars += 1;
            lines.push(SimpleLine::Assignment {
                var: aux_var.clone().into(),
                operation: *operation,
                arg0: left_var,
                arg1: right_var,
            });
            SimpleExpr::Var(aux_var)
        }
        Expression::Log2Ceil { value } => {
            let const_value = simplify_expr(value, lines, counters, array_manager, const_malloc)
                .as_constant()
                .unwrap();
            SimpleExpr::Constant(ConstExpression::Log2Ceil {
                value: Box::new(const_value),
            })
        }
    }
}

fn handle_if_condition(
    condition: &Boolean,
    then_branch: &[Line],
    else_branch: &[Line],
    res: &mut Vec<SimpleLine>,
    counters: &mut Counters,
    new_functions: &mut BTreeMap<String, SimpleFunction>,
    in_a_loop: bool,
    array_manager: &mut ArrayManager,
    const_malloc: &mut ConstMalloc,
) {
    // Transform if a == b then X else Y into if a != b then Y else X
    let (left, right, then_branch, else_branch) = match condition {
        Boolean::Equal { left, right } => (left, right, else_branch, then_branch), // switched
        Boolean::Different { left, right } => (left, right, then_branch, else_branch),
    };

    let left_simplified = simplify_expr(left, res, counters, array_manager, const_malloc);
    let right_simplified = simplify_expr(right, res, counters, array_manager, const_malloc);

    let diff_var = format!("@diff_{}", counters.aux_vars);
    counters.aux_vars += 1;
    res.push(SimpleLine::Assignment {
        var: diff_var.clone().into(),
        operation: HighLevelOperation::Sub,
        arg0: left_simplified,
        arg1: right_simplified,
    });

    let forbidden_vars_before = const_malloc.forbidden_vars.clone();

    let then_internal_vars = find_variable_usage(then_branch).0;
    let else_internal_vars = find_variable_usage(else_branch).0;
    let new_forbidden_vars = then_internal_vars
        .intersection(&else_internal_vars)
        .cloned()
        .collect::<std::collections::BTreeSet<_>>();

    const_malloc.forbidden_vars.extend(new_forbidden_vars);

    let mut array_manager_then = array_manager.clone();
    let then_branch_simplified = simplify_lines(
        then_branch,
        counters,
        new_functions,
        in_a_loop,
        &mut array_manager_then,
        const_malloc,
    );
    let mut array_manager_else = array_manager_then.clone();
    array_manager_else.valid = array_manager.valid.clone(); // Crucial: remove the access added in the IF branch

    let else_branch_simplified = simplify_lines(
        else_branch,
        counters,
        new_functions,
        in_a_loop,
        &mut array_manager_else,
        const_malloc,
    );

    const_malloc.forbidden_vars = forbidden_vars_before;

    *array_manager = array_manager_else.clone();
    // keep the intersection both branches
    array_manager.valid = array_manager
        .valid
        .intersection(&array_manager_then.valid)
        .cloned()
        .collect();

    res.push(SimpleLine::IfNotZero {
        condition: diff_var.into(),
        then_branch: then_branch_simplified,
        else_branch: else_branch_simplified,
    });
}

fn handle_for_loop(
    iterator: &Var,
    start: &Expression,
    end: &Expression,
    body: &[Line],
    rev: bool,
    unroll: bool,
    res: &mut Vec<SimpleLine>,
    counters: &mut Counters,
    new_functions: &mut BTreeMap<String, SimpleFunction>,
    in_a_loop: bool,
    array_manager: &mut ArrayManager,
    const_malloc: &mut ConstMalloc,
) {
    if unroll {
        handle_unrolled_loop(
            iterator,
            start,
            end,
            body,
            rev,
            res,
            counters,
            new_functions,
            in_a_loop,
            array_manager,
            const_malloc,
        );
        return;
    }

    if rev {
        unimplemented!("Reverse for non-unrolled loops are not implemented yet");
    }

    let mut loop_const_malloc = ConstMalloc {
        counter: const_malloc.counter,
        ..ConstMalloc::default()
    };
    let valid_aux_vars_in_array_manager_before = array_manager.valid.clone();
    array_manager.valid.clear();
    let simplified_body = simplify_lines(
        body,
        counters,
        new_functions,
        true,
        array_manager,
        &mut loop_const_malloc,
    );
    const_malloc.counter = loop_const_malloc.counter;
    array_manager.valid = valid_aux_vars_in_array_manager_before; // restore the valid aux vars

    let func_name = format!("@loop_{}", counters.loops);
    counters.loops += 1;

    // Find variables used inside loop but defined outside
    let (_, mut external_vars) = find_variable_usage(body);

    // Include variables in start/end
    for expr in [start, end] {
        for var in crate::simplify::utilities::vars_in_expression(expr) {
            external_vars.insert(var);
        }
    }
    external_vars.remove(iterator); // Iterator is internal to loop

    let mut external_vars: Vec<_> = external_vars.into_iter().collect();

    let start_simplified = simplify_expr(start, res, counters, array_manager, const_malloc);
    let end_simplified = simplify_expr(end, res, counters, array_manager, const_malloc);

    for (simplified, original) in [
        (start_simplified.clone(), start.clone()),
        (end_simplified.clone(), end.clone()),
    ] {
        if !matches!(original, Expression::Value(_)) {
            // the simplified var is auxiliary
            if let SimpleExpr::Var(var) = simplified {
                external_vars.push(var);
            }
        }
    }

    // Create function arguments: iterator + external variables
    let mut func_args = vec![iterator.clone()];
    func_args.extend(external_vars.clone());

    // Create recursive function body
    let recursive_func = create_recursive_function(
        func_name.clone(),
        func_args,
        iterator.clone(),
        end_simplified,
        simplified_body,
        &external_vars,
    );
    new_functions.insert(func_name.clone(), recursive_func);

    // Replace loop with initial function call
    let mut call_args = vec![start_simplified];
    call_args.extend(external_vars.iter().map(|v| v.clone().into()));

    res.push(SimpleLine::FunctionCall {
        function_name: func_name,
        args: call_args,
        return_data: vec![],
    });
}

fn handle_unrolled_loop(
    iterator: &Var,
    start: &Expression,
    end: &Expression,
    body: &[Line],
    rev: bool,
    res: &mut Vec<SimpleLine>,
    counters: &mut Counters,
    new_functions: &mut BTreeMap<String, SimpleFunction>,
    in_a_loop: bool,
    array_manager: &mut ArrayManager,
    const_malloc: &mut ConstMalloc,
) {
    let (internal_variables, _) = find_variable_usage(body);
    let mut unrolled_lines = Vec::new();
    let start_evaluated = start.naive_eval().unwrap().to_usize();
    let end_evaluated = end.naive_eval().unwrap().to_usize();
    let unroll_index = counters.unrolls;
    counters.unrolls += 1;

    let mut range = (start_evaluated..end_evaluated).collect::<Vec<_>>();
    if rev {
        range.reverse();
    }

    for i in range {
        let mut body_copy = body.to_vec();
        super::unroll::replace_vars_for_unroll(
            &mut body_copy,
            iterator,
            unroll_index,
            i,
            &internal_variables,
        );
        unrolled_lines.extend(simplify_lines(
            &body_copy,
            counters,
            new_functions,
            in_a_loop,
            array_manager,
            const_malloc,
        ));
    }
    res.extend(unrolled_lines);
}

fn handle_malloc(
    var: &Var,
    size: &Expression,
    vectorized: bool,
    vectorized_len: &Expression,
    res: &mut Vec<SimpleLine>,
    counters: &mut Counters,
    array_manager: &mut ArrayManager,
    const_malloc: &mut ConstMalloc,
) {
    let simplified_size = simplify_expr(size, res, counters, array_manager, const_malloc);
    let simplified_vectorized_len =
        simplify_expr(vectorized_len, res, counters, array_manager, const_malloc);
    if simplified_size.is_constant() && !vectorized && const_malloc.forbidden_vars.contains(var) {
        println!("TODO: Optimization missed: Requires to align const malloc in if/else branches");
    }
    match simplified_size {
        SimpleExpr::Constant(const_size)
            if !vectorized && !const_malloc.forbidden_vars.contains(var) =>
        {
            // TODO do this optimization even if we are in an if/else branch
            let label = const_malloc.counter;
            const_malloc.counter += 1;
            const_malloc.map.insert(var.clone(), label);
            res.push(SimpleLine::ConstMalloc {
                var: var.clone(),
                size: const_size,
                label,
            });
        }
        _ => {
            res.push(SimpleLine::HintMAlloc {
                var: var.clone(),
                size: simplified_size,
                vectorized: vectorized,
                vectorized_len: simplified_vectorized_len,
            });
        }
    }
}

/// Handle array access assignment operations.
pub fn handle_array_assignment(
    counters: &mut Counters,
    res: &mut Vec<SimpleLine>,
    array: SimpleExpr,
    index: &Expression,
    access_type: ArrayAccessType,
    array_manager: &mut ArrayManager,
    const_malloc: &ConstMalloc,
) {
    let simplified_index = simplify_expr(index, res, counters, array_manager, const_malloc);

    if let SimpleExpr::Constant(offset) = simplified_index.clone()
        && let SimpleExpr::Var(array_var) = &array
        && let Some(label) = const_malloc.map.get(array_var)
        && let ArrayAccessType::ArrayIsAssigned(Expression::Binary {
            left,
            operation,
            right,
        }) = &access_type
    {
        let arg0 = simplify_expr(left, res, counters, array_manager, const_malloc);
        let arg1 = simplify_expr(right, res, counters, array_manager, const_malloc);
        res.push(SimpleLine::Assignment {
            var: VarOrConstMallocAccess::ConstMallocAccess {
                malloc_label: *label,
                offset,
            },
            operation: *operation,
            arg0,
            arg1,
        });
        return;
    }

    let value_simplified = match access_type {
        ArrayAccessType::VarIsAssigned(var) => SimpleExpr::Var(var),
        ArrayAccessType::ArrayIsAssigned(expr) => {
            simplify_expr(&expr, res, counters, array_manager, const_malloc)
        }
    };

    // TODO opti: in some case we could use ConstMallocAccess

    let (index_var, shift) = match simplified_index {
        SimpleExpr::Constant(c) => (array, c),
        _ => {
            // Create pointer variable: ptr = array + index
            let ptr_var = format!("@aux_var_{}", counters.aux_vars);
            counters.aux_vars += 1;
            res.push(SimpleLine::Assignment {
                var: ptr_var.clone().into(),
                operation: HighLevelOperation::Add,
                arg0: array,
                arg1: simplified_index,
            });
            (SimpleExpr::Var(ptr_var), ConstExpression::zero())
        }
    };

    res.push(SimpleLine::RawAccess {
        res: value_simplified,
        index: index_var,
        shift,
    });
}

fn create_recursive_function(
    name: String,
    args: Vec<Var>,
    iterator: Var,
    end: SimpleExpr,
    mut body: Vec<SimpleLine>,
    external_vars: &[Var],
) -> SimpleFunction {
    // Add iterator increment
    let next_iter = format!("@incremented_{iterator}");
    body.push(SimpleLine::Assignment {
        var: next_iter.clone().into(),
        operation: HighLevelOperation::Add,
        arg0: iterator.clone().into(),
        arg1: SimpleExpr::one(),
    });

    // Add recursive call
    let mut recursive_args: Vec<SimpleExpr> = vec![next_iter.into()];
    recursive_args.extend(external_vars.iter().map(|v| v.clone().into()));

    body.push(SimpleLine::FunctionCall {
        function_name: name.clone(),
        args: recursive_args,
        return_data: vec![],
    });
    body.push(SimpleLine::FunctionRet {
        return_data: vec![],
    });

    let diff_var = format!("@diff_{iterator}");

    let instructions = vec![
        SimpleLine::Assignment {
            var: diff_var.clone().into(),
            operation: HighLevelOperation::Sub,
            arg0: iterator.into(),
            arg1: end,
        },
        SimpleLine::IfNotZero {
            condition: diff_var.into(),
            then_branch: body,
            else_branch: vec![SimpleLine::FunctionRet {
                return_data: vec![],
            }],
        },
    ];

    SimpleFunction {
        name,
        arguments: args,
        n_returned_vars: 0,
        instructions,
    }
}
