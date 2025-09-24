use crate::{
    Counter, F,
    intermediate_bytecode::HighLevelOperation,
    lang::{
        Boolean, ConstExpression, ConstMallocLabel, Expression, Function, Line, Program,
        SimpleExpr, Var,
    },
    precompiles::Precompile,
};
use lean_vm::SourceLineNumber;
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::{Display, Formatter},
};
use utils::ToUsize;

#[derive(Debug, Clone)]
pub struct SimpleProgram {
    pub functions: BTreeMap<String, SimpleFunction>,
}

#[derive(Debug, Clone)]
pub struct SimpleFunction {
    pub name: String,
    pub arguments: Vec<Var>,
    pub n_returned_vars: usize,
    pub instructions: Vec<SimpleLine>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VarOrConstMallocAccess {
    Var(Var),
    ConstMallocAccess {
        malloc_label: ConstMallocLabel,
        offset: ConstExpression,
    },
}

impl From<VarOrConstMallocAccess> for SimpleExpr {
    fn from(var_or_const: VarOrConstMallocAccess) -> Self {
        match var_or_const {
            VarOrConstMallocAccess::Var(var) => Self::Var(var),
            VarOrConstMallocAccess::ConstMallocAccess {
                malloc_label,
                offset,
            } => Self::ConstMallocAccess {
                malloc_label,
                offset,
            },
        }
    }
}

impl TryInto<VarOrConstMallocAccess> for SimpleExpr {
    type Error = ();

    fn try_into(self) -> Result<VarOrConstMallocAccess, Self::Error> {
        match self {
            Self::Var(var) => Ok(VarOrConstMallocAccess::Var(var)),
            Self::ConstMallocAccess {
                malloc_label,
                offset,
            } => Ok(VarOrConstMallocAccess::ConstMallocAccess {
                malloc_label,
                offset,
            }),
            _ => Err(()),
        }
    }
}

impl From<Var> for VarOrConstMallocAccess {
    fn from(var: Var) -> Self {
        Self::Var(var)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SimpleLine {
    Match {
        value: SimpleExpr,
        arms: Vec<Vec<Self>>, // patterns = 0, 1, ...
    },
    Assignment {
        var: VarOrConstMallocAccess,
        operation: HighLevelOperation,
        arg0: SimpleExpr,
        arg1: SimpleExpr,
    },
    RawAccess {
        res: SimpleExpr,
        index: SimpleExpr,
        shift: ConstExpression,
    }, // res = memory[index + shift]
    IfNotZero {
        condition: SimpleExpr,
        then_branch: Vec<Self>,
        else_branch: Vec<Self>,
    },
    FunctionCall {
        function_name: String,
        args: Vec<SimpleExpr>,
        return_data: Vec<Var>,
    },
    FunctionRet {
        return_data: Vec<SimpleExpr>,
    },
    Precompile {
        precompile: Precompile,
        args: Vec<SimpleExpr>,
    },
    Panic,
    // Hints
    DecomposeBits {
        var: Var, // a pointer to 31 * len(to_decompose) field elements, containing the bits of "to_decompose"
        to_decompose: Vec<SimpleExpr>,
        label: ConstMallocLabel,
    },
    CounterHint {
        var: Var,
    },
    Print {
        line_info: String,
        content: Vec<SimpleExpr>,
    },
    HintMAlloc {
        var: Var,
        size: SimpleExpr,
        vectorized: bool,
        vectorized_len: SimpleExpr,
    },
    ConstMalloc {
        // always not vectorized
        var: Var,
        size: ConstExpression,
        label: ConstMallocLabel,
    },
    // noop, debug purpose only
    LocationReport {
        location: SourceLineNumber,
    },
}

pub fn simplify_program(mut program: Program) -> SimpleProgram {
    handle_inlined_functions(&mut program);
    handle_const_arguments(&mut program);
    let mut new_functions = BTreeMap::new();
    let mut counters = Counters::default();
    let mut const_malloc = ConstMalloc::default();
    for (name, func) in &program.functions {
        let mut array_manager = ArrayManager::default();
        let simplified_instructions = simplify_lines(
            &func.body,
            &mut counters,
            &mut new_functions,
            false,
            &mut array_manager,
            &mut const_malloc,
        );
        let arguments = func
            .arguments
            .iter()
            .map(|(v, is_const)| {
                assert!(!is_const,);
                v.clone()
            })
            .collect::<Vec<_>>();
        new_functions.insert(
            name.clone(),
            SimpleFunction {
                name: name.clone(),
                arguments,
                n_returned_vars: func.n_returned_vars,
                instructions: simplified_instructions,
            },
        );
        const_malloc.map.clear();
    }
    SimpleProgram {
        functions: new_functions,
    }
}

#[derive(Debug, Clone, Default)]
struct Counters {
    aux_vars: usize,
    loops: usize,
    unrolls: usize,
}

#[derive(Debug, Clone, Default)]
struct ArrayManager {
    counter: usize,
    aux_vars: BTreeMap<(SimpleExpr, Expression), Var>, // (array, index) -> aux_var
    valid: BTreeSet<Var>,                              // currently valid aux vars
}

#[derive(Debug, Clone, Default)]
pub struct ConstMalloc {
    counter: usize,
    map: BTreeMap<Var, ConstMallocLabel>,
    forbidden_vars: BTreeSet<Var>, // vars shared between branches of an if/else
}

impl ArrayManager {
    fn get_aux_var(&mut self, array: &SimpleExpr, index: &Expression) -> Var {
        if let Some(var) = self.aux_vars.get(&(array.clone(), index.clone())) {
            return var.clone();
        }
        let new_var = format!("@arr_aux_{}", self.counter);
        self.counter += 1;
        self.aux_vars
            .insert((array.clone(), index.clone()), new_var.clone());
        new_var
    }
}

fn simplify_lines(
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
                // Transform if a == b then X else Y into if a != b then Y else X

                let (left, right, then_branch, else_branch) = match condition {
                    Boolean::Equal { left, right } => (left, right, else_branch, then_branch), // switched
                    Boolean::Different { left, right } => (left, right, then_branch, else_branch),
                };

                let left_simplified =
                    simplify_expr(left, &mut res, counters, array_manager, const_malloc);
                let right_simplified =
                    simplify_expr(right, &mut res, counters, array_manager, const_malloc);

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
                    .collect::<BTreeSet<_>>();

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
            Line::ForLoop {
                iterator,
                start,
                end,
                body,
                rev,
                unroll,
            } => {
                if *unroll {
                    let (internal_variables, _) = find_variable_usage(body);
                    let mut unrolled_lines = Vec::new();
                    let start_evaluated = start.naive_eval().unwrap().to_usize();
                    let end_evaluated = end.naive_eval().unwrap().to_usize();
                    let unroll_index = counters.unrolls;
                    counters.unrolls += 1;

                    let mut range = (start_evaluated..end_evaluated).collect::<Vec<_>>();
                    if *rev {
                        range.reverse();
                    }

                    for i in range {
                        let mut body_copy = body.clone();
                        replace_vars_for_unroll(
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
                    continue;
                }

                if *rev {
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
                    for var in vars_in_expression(expr) {
                        external_vars.insert(var);
                    }
                }
                external_vars.remove(iterator); // Iterator is internal to loop

                let mut external_vars: Vec<_> = external_vars.into_iter().collect();

                let start_simplified =
                    simplify_expr(start, &mut res, counters, array_manager, const_malloc);
                let end_simplified =
                    simplify_expr(end, &mut res, counters, array_manager, const_malloc);

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
                let simplified_size =
                    simplify_expr(size, &mut res, counters, array_manager, const_malloc);
                let simplified_vectorized_len = simplify_expr(
                    vectorized_len,
                    &mut res,
                    counters,
                    array_manager,
                    const_malloc,
                );
                if simplified_size.is_constant()
                    && !*vectorized
                    && const_malloc.forbidden_vars.contains(var)
                {
                    println!(
                        "TODO: Optimization missed: Requires to align const malloc in if/else branches"
                    );
                }
                match simplified_size {
                    SimpleExpr::Constant(const_size)
                        if !*vectorized && !const_malloc.forbidden_vars.contains(var) =>
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
                            vectorized: *vectorized,
                            vectorized_len: simplified_vectorized_len,
                        });
                    }
                }
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

fn simplify_expr(
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

/// Returns (internal_vars, external_vars)
pub fn find_variable_usage(lines: &[Line]) -> (BTreeSet<Var>, BTreeSet<Var>) {
    let mut internal_vars = BTreeSet::new();
    let mut external_vars = BTreeSet::new();

    let on_new_expr =
        |expr: &Expression, internal_vars: &BTreeSet<Var>, external_vars: &mut BTreeSet<Var>| {
            for var in vars_in_expression(expr) {
                if !internal_vars.contains(&var) {
                    external_vars.insert(var);
                }
            }
        };

    let on_new_condition =
        |condition: &Boolean, internal_vars: &BTreeSet<Var>, external_vars: &mut BTreeSet<Var>| {
            let (Boolean::Equal { left, right } | Boolean::Different { left, right }) = condition;
            on_new_expr(left, internal_vars, external_vars);
            on_new_expr(right, internal_vars, external_vars);
        };

    for line in lines {
        match line {
            Line::Match { value, arms } => {
                on_new_expr(value, &internal_vars, &mut external_vars);
                for (_, statements) in arms {
                    let (stmt_internal, stmt_external) = find_variable_usage(statements);
                    internal_vars.extend(stmt_internal);
                    external_vars.extend(
                        stmt_external
                            .into_iter()
                            .filter(|v| !internal_vars.contains(v)),
                    );
                }
            }
            Line::Assignment { var, value } => {
                on_new_expr(value, &internal_vars, &mut external_vars);
                internal_vars.insert(var.clone());
            }
            Line::IfCondition {
                condition,
                then_branch,
                else_branch,
            } => {
                on_new_condition(condition, &internal_vars, &mut external_vars);

                let (then_internal, then_external) = find_variable_usage(then_branch);
                let (else_internal, else_external) = find_variable_usage(else_branch);

                internal_vars.extend(then_internal.union(&else_internal).cloned());
                external_vars.extend(
                    then_external
                        .union(&else_external)
                        .filter(|v| !internal_vars.contains(*v))
                        .cloned(),
                );
            }
            Line::FunctionCall {
                args, return_data, ..
            } => {
                for arg in args {
                    on_new_expr(arg, &internal_vars, &mut external_vars);
                }
                internal_vars.extend(return_data.iter().cloned());
            }
            Line::Assert(condition) => {
                on_new_condition(condition, &internal_vars, &mut external_vars);
            }
            Line::FunctionRet { return_data } => {
                for ret in return_data {
                    on_new_expr(ret, &internal_vars, &mut external_vars);
                }
            }
            Line::MAlloc { var, size, .. } => {
                on_new_expr(size, &internal_vars, &mut external_vars);
                internal_vars.insert(var.clone());
            }
            Line::Precompile {
                precompile: _,
                args,
            } => {
                for arg in args {
                    on_new_expr(arg, &internal_vars, &mut external_vars);
                }
            }
            Line::Print { content, .. } => {
                for var in content {
                    on_new_expr(var, &internal_vars, &mut external_vars);
                }
            }
            Line::DecomposeBits { var, to_decompose } => {
                for expr in to_decompose {
                    on_new_expr(expr, &internal_vars, &mut external_vars);
                }
                internal_vars.insert(var.clone());
            }
            Line::CounterHint { var } => {
                internal_vars.insert(var.clone());
            }
            Line::ForLoop {
                iterator,
                start,
                end,
                body,
                rev: _,
                unroll: _,
            } => {
                let (body_internal, body_external) = find_variable_usage(body);
                internal_vars.extend(body_internal);
                internal_vars.insert(iterator.clone());
                external_vars.extend(body_external.difference(&internal_vars).cloned());
                on_new_expr(start, &internal_vars, &mut external_vars);
                on_new_expr(end, &internal_vars, &mut external_vars);
            }
            Line::ArrayAssign {
                array,
                index,
                value,
            } => {
                on_new_expr(&array.clone().into(), &internal_vars, &mut external_vars);
                on_new_expr(index, &internal_vars, &mut external_vars);
                on_new_expr(value, &internal_vars, &mut external_vars);
            }
            Line::Panic | Line::Break | Line::LocationReport { .. } => {}
        }
    }

    (internal_vars, external_vars)
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

fn vars_in_expression(expr: &Expression) -> BTreeSet<Var> {
    let mut vars = BTreeSet::new();
    match expr {
        Expression::Value(value) => {
            if let SimpleExpr::Var(var) = value {
                vars.insert(var.clone());
            }
        }
        Expression::ArrayAccess { array, index } => {
            if let SimpleExpr::Var(array) = array {
                vars.insert(array.clone());
            }
            vars.extend(vars_in_expression(index));
        }
        Expression::Binary { left, right, .. } => {
            vars.extend(vars_in_expression(left));
            vars.extend(vars_in_expression(right));
        }
        Expression::Log2Ceil { value } => {
            vars.extend(vars_in_expression(value));
        }
    }
    vars
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ArrayAccessType {
    VarIsAssigned(Var),          // var = array[index]
    ArrayIsAssigned(Expression), // array[index] = expr
}

fn handle_array_assignment(
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

fn replace_vars_for_unroll_in_expr(
    expr: &mut Expression,
    iterator: &Var,
    unroll_index: usize,
    iterator_value: usize,
    internal_vars: &BTreeSet<Var>,
) {
    match expr {
        Expression::Value(value_expr) => match value_expr {
            SimpleExpr::Var(var) => {
                if var == iterator {
                    *value_expr = SimpleExpr::Constant(ConstExpression::from(iterator_value));
                } else if internal_vars.contains(var) {
                    *var = format!("@unrolled_{unroll_index}_{iterator_value}_{var}");
                }
            }
            SimpleExpr::Constant(_) | SimpleExpr::ConstMallocAccess { .. } => {}
        },
        Expression::ArrayAccess { array, index } => {
            if let SimpleExpr::Var(array_var) = array {
                assert!(array_var != iterator, "Weird");
                if internal_vars.contains(array_var) {
                    *array_var = format!("@unrolled_{unroll_index}_{iterator_value}_{array_var}");
                }
            }

            replace_vars_for_unroll_in_expr(
                index,
                iterator,
                unroll_index,
                iterator_value,
                internal_vars,
            );
        }
        Expression::Binary { left, right, .. } => {
            replace_vars_for_unroll_in_expr(
                left,
                iterator,
                unroll_index,
                iterator_value,
                internal_vars,
            );
            replace_vars_for_unroll_in_expr(
                right,
                iterator,
                unroll_index,
                iterator_value,
                internal_vars,
            );
        }
        Expression::Log2Ceil { value } => {
            replace_vars_for_unroll_in_expr(
                value,
                iterator,
                unroll_index,
                iterator_value,
                internal_vars,
            );
        }
    }
}

fn replace_vars_for_unroll(
    lines: &mut [Line],
    iterator: &Var,
    unroll_index: usize,
    iterator_value: usize,
    internal_vars: &BTreeSet<Var>,
) {
    for line in lines {
        match line {
            Line::Match { value, arms } => {
                replace_vars_for_unroll_in_expr(
                    value,
                    iterator,
                    unroll_index,
                    iterator_value,
                    internal_vars,
                );
                for (_, statements) in arms {
                    replace_vars_for_unroll(
                        statements,
                        iterator,
                        unroll_index,
                        iterator_value,
                        internal_vars,
                    );
                }
            }
            Line::Assignment { var, value } => {
                assert!(var != iterator, "Weird");
                *var = format!("@unrolled_{unroll_index}_{iterator_value}_{var}");
                replace_vars_for_unroll_in_expr(
                    value,
                    iterator,
                    unroll_index,
                    iterator_value,
                    internal_vars,
                );
            }
            Line::ArrayAssign {
                // array[index] = value
                array,
                index,
                value,
            } => {
                if let SimpleExpr::Var(array_var) = array {
                    assert!(array_var != iterator, "Weird");
                    if internal_vars.contains(array_var) {
                        *array_var =
                            format!("@unrolled_{unroll_index}_{iterator_value}_{array_var}");
                    }
                }
                replace_vars_for_unroll_in_expr(
                    index,
                    iterator,
                    unroll_index,
                    iterator_value,
                    internal_vars,
                );
                replace_vars_for_unroll_in_expr(
                    value,
                    iterator,
                    unroll_index,
                    iterator_value,
                    internal_vars,
                );
            }
            Line::Assert(Boolean::Equal { left, right } | Boolean::Different { left, right }) => {
                replace_vars_for_unroll_in_expr(
                    left,
                    iterator,
                    unroll_index,
                    iterator_value,
                    internal_vars,
                );
                replace_vars_for_unroll_in_expr(
                    right,
                    iterator,
                    unroll_index,
                    iterator_value,
                    internal_vars,
                );
            }
            Line::IfCondition {
                condition: Boolean::Equal { left, right } | Boolean::Different { left, right },
                then_branch,
                else_branch,
            } => {
                replace_vars_for_unroll_in_expr(
                    left,
                    iterator,
                    unroll_index,
                    iterator_value,
                    internal_vars,
                );
                replace_vars_for_unroll_in_expr(
                    right,
                    iterator,
                    unroll_index,
                    iterator_value,
                    internal_vars,
                );
                replace_vars_for_unroll(
                    then_branch,
                    iterator,
                    unroll_index,
                    iterator_value,
                    internal_vars,
                );
                replace_vars_for_unroll(
                    else_branch,
                    iterator,
                    unroll_index,
                    iterator_value,
                    internal_vars,
                );
            }
            Line::ForLoop {
                iterator: other_iterator,
                start,
                end,
                body,
                rev: _,
                unroll: _,
            } => {
                assert!(other_iterator != iterator);
                *other_iterator =
                    format!("@unrolled_{unroll_index}_{iterator_value}_{other_iterator}");
                replace_vars_for_unroll_in_expr(
                    start,
                    iterator,
                    unroll_index,
                    iterator_value,
                    internal_vars,
                );
                replace_vars_for_unroll_in_expr(
                    end,
                    iterator,
                    unroll_index,
                    iterator_value,
                    internal_vars,
                );
                replace_vars_for_unroll(
                    body,
                    iterator,
                    unroll_index,
                    iterator_value,
                    internal_vars,
                );
            }
            Line::FunctionCall {
                function_name: _,
                args,
                return_data,
            } => {
                // Function calls are not unrolled, so we don't need to change them
                for arg in args {
                    replace_vars_for_unroll_in_expr(
                        arg,
                        iterator,
                        unroll_index,
                        iterator_value,
                        internal_vars,
                    );
                }
                for ret in return_data {
                    *ret = format!("@unrolled_{unroll_index}_{iterator_value}_{ret}");
                }
            }
            Line::FunctionRet { return_data } => {
                for ret in return_data {
                    replace_vars_for_unroll_in_expr(
                        ret,
                        iterator,
                        unroll_index,
                        iterator_value,
                        internal_vars,
                    );
                }
            }
            Line::Precompile {
                precompile: _,
                args,
            } => {
                for arg in args {
                    replace_vars_for_unroll_in_expr(
                        arg,
                        iterator,
                        unroll_index,
                        iterator_value,
                        internal_vars,
                    );
                }
            }
            Line::Print { line_info, content } => {
                // Print statements are not unrolled, so we don't need to change them
                *line_info += &format!(" (unrolled {unroll_index} {iterator_value})");
                for var in content {
                    replace_vars_for_unroll_in_expr(
                        var,
                        iterator,
                        unroll_index,
                        iterator_value,
                        internal_vars,
                    );
                }
            }
            Line::MAlloc {
                var,
                size,
                vectorized: _,
                vectorized_len,
            } => {
                assert!(var != iterator, "Weird");
                *var = format!("@unrolled_{unroll_index}_{iterator_value}_{var}");
                replace_vars_for_unroll_in_expr(
                    size,
                    iterator,
                    unroll_index,
                    iterator_value,
                    internal_vars,
                );
                replace_vars_for_unroll_in_expr(
                    vectorized_len,
                    iterator,
                    unroll_index,
                    iterator_value,
                    internal_vars,
                );
            }
            Line::DecomposeBits { var, to_decompose } => {
                assert!(var != iterator, "Weird");
                *var = format!("@unrolled_{unroll_index}_{iterator_value}_{var}");
                for expr in to_decompose {
                    replace_vars_for_unroll_in_expr(
                        expr,
                        iterator,
                        unroll_index,
                        iterator_value,
                        internal_vars,
                    );
                }
            }
            Line::CounterHint { var } => {
                *var = format!("@unrolled_{unroll_index}_{iterator_value}_{var}");
            }
            Line::Break | Line::Panic | Line::LocationReport { .. } => {}
        }
    }
}

fn handle_inlined_functions(program: &mut Program) {
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

    for func in program.functions.values_mut() {
        if func.inlined {
            let mut func_called = Vec::new();
            get_function_called(&func.body, &mut func_called);
            for func_called in func_called {
                assert!(
                    !inlined_functions.contains_key(&func_called),
                    "Inlined functions calling other inlined functions are not supported yet"
                );
            }
        } else {
            handle_inlined_functions_helper(
                &mut func.body,
                &inlined_functions,
                &mut Counter::new(),
                &mut Counter::new(),
            );
        }
    }

    for func in inlined_functions.keys() {
        program.functions.remove(func);
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

fn handle_const_arguments(program: &mut Program) {
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
    while changed {
        changed = false;
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

fn replace_vars_by_const_in_expr(expr: &mut Expression, map: &BTreeMap<Var, F>) {
    match expr {
        Expression::Value(value) => match &value {
            SimpleExpr::Var(var) => {
                if let Some(const_value) = map.get(var) {
                    *value = SimpleExpr::scalar(const_value.to_usize());
                }
            }
            SimpleExpr::ConstMallocAccess { .. } => {
                unreachable!()
            }
            SimpleExpr::Constant(_) => {}
        },
        Expression::ArrayAccess { array, index } => {
            if let SimpleExpr::Var(array_var) = array {
                assert!(
                    !map.contains_key(array_var),
                    "Array {array_var} is a constant"
                );
            }
            replace_vars_by_const_in_expr(index, map);
        }
        Expression::Binary { left, right, .. } => {
            replace_vars_by_const_in_expr(left, map);
            replace_vars_by_const_in_expr(right, map);
        }
        Expression::Log2Ceil { value } => {
            replace_vars_by_const_in_expr(value, map);
        }
    }
}

fn get_function_called(lines: &[Line], function_called: &mut Vec<String>) {
    for line in lines {
        match line {
            Line::Match { value: _, arms } => {
                for (_, statements) in arms {
                    get_function_called(statements, function_called);
                }
            }
            Line::FunctionCall { function_name, .. } => {
                function_called.push(function_name.clone());
            }
            Line::IfCondition {
                then_branch,
                else_branch,
                ..
            } => {
                get_function_called(then_branch, function_called);
                get_function_called(else_branch, function_called);
            }
            Line::ForLoop { body, .. } => {
                get_function_called(body, function_called);
            }
            Line::Assignment { .. }
            | Line::ArrayAssign { .. }
            | Line::Assert { .. }
            | Line::FunctionRet { .. }
            | Line::Precompile { .. }
            | Line::Print { .. }
            | Line::DecomposeBits { .. }
            | Line::CounterHint { .. }
            | Line::MAlloc { .. }
            | Line::Panic
            | Line::Break
            | Line::LocationReport { .. } => {}
        }
    }
}

fn replace_vars_by_const_in_lines(lines: &mut [Line], map: &BTreeMap<Var, F>) {
    for line in lines {
        match line {
            Line::Match { value, arms } => {
                replace_vars_by_const_in_expr(value, map);
                for (_, statements) in arms {
                    replace_vars_by_const_in_lines(statements, map);
                }
            }
            Line::Assignment { var, value } => {
                assert!(!map.contains_key(var), "Variable {var} is a constant");
                replace_vars_by_const_in_expr(value, map);
            }
            Line::ArrayAssign {
                array,
                index,
                value,
            } => {
                if let SimpleExpr::Var(array_var) = array {
                    assert!(
                        !map.contains_key(array_var),
                        "Array {array_var} is a constant"
                    );
                }
                replace_vars_by_const_in_expr(index, map);
                replace_vars_by_const_in_expr(value, map);
            }
            Line::FunctionCall {
                args, return_data, ..
            } => {
                for arg in args {
                    replace_vars_by_const_in_expr(arg, map);
                }
                for ret in return_data {
                    assert!(
                        !map.contains_key(ret),
                        "Return variable {ret} is a constant"
                    );
                }
            }
            Line::IfCondition {
                condition,
                then_branch,
                else_branch,
            } => {
                match condition {
                    Boolean::Equal { left, right } | Boolean::Different { left, right } => {
                        replace_vars_by_const_in_expr(left, map);
                        replace_vars_by_const_in_expr(right, map);
                    }
                }
                replace_vars_by_const_in_lines(then_branch, map);
                replace_vars_by_const_in_lines(else_branch, map);
            }
            Line::ForLoop {
                body, start, end, ..
            } => {
                replace_vars_by_const_in_expr(start, map);
                replace_vars_by_const_in_expr(end, map);
                replace_vars_by_const_in_lines(body, map);
            }
            Line::Assert(condition) => match condition {
                Boolean::Equal { left, right } | Boolean::Different { left, right } => {
                    replace_vars_by_const_in_expr(left, map);
                    replace_vars_by_const_in_expr(right, map);
                }
            },
            Line::FunctionRet { return_data } => {
                for ret in return_data {
                    replace_vars_by_const_in_expr(ret, map);
                }
            }
            Line::Precompile {
                precompile: _,
                args,
            } => {
                for arg in args {
                    replace_vars_by_const_in_expr(arg, map);
                }
            }
            Line::Print { content, .. } => {
                for var in content {
                    replace_vars_by_const_in_expr(var, map);
                }
            }
            Line::DecomposeBits { var, to_decompose } => {
                assert!(!map.contains_key(var), "Variable {var} is a constant");
                for expr in to_decompose {
                    replace_vars_by_const_in_expr(expr, map);
                }
            }
            Line::CounterHint { var } => {
                assert!(!map.contains_key(var), "Variable {var} is a constant");
            }
            Line::MAlloc { var, size, .. } => {
                assert!(!map.contains_key(var), "Variable {var} is a constant");
                replace_vars_by_const_in_expr(size, map);
            }
            Line::Panic | Line::Break | Line::LocationReport { .. } => {}
        }
    }
}
impl Display for SimpleLine {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_string_with_indent(0))
    }
}

impl Display for VarOrConstMallocAccess {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Var(var) => write!(f, "{var}"),
            Self::ConstMallocAccess {
                malloc_label,
                offset,
            } => {
                write!(f, "ConstMallocAccess({malloc_label}, {offset})")
            }
        }
    }
}

impl SimpleLine {
    fn to_string_with_indent(&self, indent: usize) -> String {
        let spaces = "    ".repeat(indent);
        let line_str = match self {
            Self::Match { value, arms } => {
                let arms_str = arms
                    .iter()
                    .enumerate()
                    .map(|(pattern, stmt)| {
                        format!(
                            "{} => {}",
                            pattern,
                            stmt.iter()
                                .map(|line| line.to_string_with_indent(indent + 1))
                                .collect::<Vec<_>>()
                                .join("\n")
                        )
                    })
                    .collect::<Vec<_>>()
                    .join(", ");

                format!("match {value} {{\n{arms_str}\n{spaces}}}")
            }
            Self::Assignment {
                var,
                operation,
                arg0,
                arg1,
            } => {
                format!("{var} = {arg0} {operation} {arg1}")
            }
            Self::DecomposeBits {
                var: result,
                to_decompose,
                label: _,
            } => {
                format!(
                    "{} = decompose_bits({})",
                    result,
                    to_decompose
                        .iter()
                        .map(|expr| format!("{expr}"))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            Self::CounterHint { var: result } => {
                format!("{result} = counter_hint()")
            }
            Self::RawAccess { res, index, shift } => {
                format!("memory[{index} + {shift}] = {res}")
            }
            Self::IfNotZero {
                condition,
                then_branch,
                else_branch,
            } => {
                let then_str = then_branch
                    .iter()
                    .map(|line| line.to_string_with_indent(indent + 1))
                    .collect::<Vec<_>>()
                    .join("\n");

                let else_str = else_branch
                    .iter()
                    .map(|line| line.to_string_with_indent(indent + 1))
                    .collect::<Vec<_>>()
                    .join("\n");

                if else_branch.is_empty() {
                    format!("if {condition} != 0 {{\n{then_str}\n{spaces}}}")
                } else {
                    format!(
                        "if {condition} != 0 {{\n{then_str}\n{spaces}}} else {{\n{else_str}\n{spaces}}}"
                    )
                }
            }
            Self::FunctionCall {
                function_name,
                args,
                return_data,
            } => {
                let args_str = args
                    .iter()
                    .map(|arg| format!("{arg}"))
                    .collect::<Vec<_>>()
                    .join(", ");
                let return_data_str = return_data
                    .iter()
                    .map(|var| var.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");

                if return_data.is_empty() {
                    format!("{function_name}({args_str})")
                } else {
                    format!("{return_data_str} = {function_name}({args_str})")
                }
            }
            Self::FunctionRet { return_data } => {
                let return_data_str = return_data
                    .iter()
                    .map(|arg| format!("{arg}"))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("return {return_data_str}")
            }
            Self::Precompile { precompile, args } => {
                format!(
                    "{}({})",
                    &precompile.name,
                    args.iter()
                        .map(|arg| format!("{arg}"))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            Self::Print {
                line_info: _,
                content,
            } => {
                let content_str = content
                    .iter()
                    .map(|c| format!("{c}"))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("print({content_str})")
            }
            Self::HintMAlloc {
                var,
                size,
                vectorized,
                vectorized_len,
            } => {
                if *vectorized {
                    format!("{var} = malloc_vec({size}, {vectorized_len})")
                } else {
                    format!("{var} = malloc({size})")
                }
            }
            Self::ConstMalloc {
                var,
                size,
                label: _,
            } => {
                format!("{var} = malloc({size})")
            }
            Self::Panic => "panic".to_string(),
            Self::LocationReport { .. } => Default::default(),
        };
        format!("{spaces}{line_str}")
    }
}

impl Display for SimpleFunction {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let args_str = self
            .arguments
            .iter()
            .map(|arg| arg.to_string())
            .collect::<Vec<_>>()
            .join(", ");

        let instructions_str = self
            .instructions
            .iter()
            .map(|line| line.to_string_with_indent(1))
            .collect::<Vec<_>>()
            .join("\n");

        if self.instructions.is_empty() {
            write!(
                f,
                "fn {}({}) -> {} {{}}",
                self.name, args_str, self.n_returned_vars
            )
        } else {
            write!(
                f,
                "fn {}({}) -> {} {{\n{}\n}}",
                self.name, args_str, self.n_returned_vars, instructions_str
            )
        }
    }
}

impl Display for SimpleProgram {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut first = true;
        for function in self.functions.values() {
            if !first {
                writeln!(f)?;
            }
            write!(f, "{function}")?;
            first = false;
        }
        Ok(())
    }
}
