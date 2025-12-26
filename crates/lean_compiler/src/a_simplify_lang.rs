use crate::{
    Counter, F,
    ir::HighLevelOperation,
    lang::{
        AssignmentTarget, AssumeBoolean, Condition, ConstExpression, ConstMallocLabel, ConstantValue, Context,
        Expression, Function, Line, Program, Scope, SimpleExpr, Var,
    },
    parser::ConstArrayValue,
};
use lean_vm::{Boolean, BooleanExpr, CustomHint, FileId, SourceLineNumber, SourceLocation, Table, TableT};
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
    pub file_id: FileId,
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
            VarOrConstMallocAccess::ConstMallocAccess { malloc_label, offset } => {
                Self::ConstMallocAccess { malloc_label, offset }
            }
        }
    }
}

impl TryInto<VarOrConstMallocAccess> for SimpleExpr {
    type Error = ();

    fn try_into(self) -> Result<VarOrConstMallocAccess, Self::Error> {
        match self {
            Self::Var(var) => Ok(VarOrConstMallocAccess::Var(var)),
            Self::ConstMallocAccess { malloc_label, offset } => {
                Ok(VarOrConstMallocAccess::ConstMallocAccess { malloc_label, offset })
            }
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
    ForwardDeclaration {
        var: Var,
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
        line_number: SourceLineNumber,
    },
    TestZero {
        // Test that the result of the given operation is zero
        operation: HighLevelOperation,
        arg0: SimpleExpr,
        arg1: SimpleExpr,
    },
    FunctionCall {
        function_name: String,
        args: Vec<SimpleExpr>,
        return_data: Vec<Var>,
        line_number: SourceLineNumber,
    },
    FunctionRet {
        return_data: Vec<SimpleExpr>,
    },
    Precompile {
        table: Table,
        args: Vec<SimpleExpr>,
    },
    Panic,
    // Hints
    /// each field element x is decomposed to: (a0, a1, a2, ..., a11, b) where:
    /// x = a0 + a1.4 + a2.4^2 + a3.4^3 + ... + a11.4^11 + b.2^24
    /// and ai < 4, b < 2^7 - 1
    /// The decomposition is unique, and always exists (except for x = -1)
    CustomHint(CustomHint, Vec<SimpleExpr>),
    PrivateInputStart {
        result: Var,
    },
    Print {
        line_info: String,
        content: Vec<SimpleExpr>,
    },
    HintMAlloc {
        var: Var,
        size: SimpleExpr,
    },
    ConstMalloc {
        // always not vectorized
        var: Var,
        size: ConstExpression,
        label: ConstMallocLabel,
    },
    // noop, debug purpose only
    LocationReport {
        location: SourceLocation,
    },
    DebugAssert(BooleanExpr<SimpleExpr>, SourceLineNumber),
}

pub fn simplify_program(mut program: Program) -> SimpleProgram {
    check_program_scoping(&program);
    handle_inlined_functions(&mut program);

    // Iterate between unrolling and const argument handling until fixed point
    let mut unroll_counter = Counter::new();
    let mut max_iterations = 100;
    loop {
        let mut any_change = false;

        any_change |= unroll_loops_in_program(&mut program, &mut unroll_counter);
        any_change |= handle_const_arguments(&mut program);

        max_iterations -= 1;
        assert!(max_iterations > 0, "Too many iterations while simplifying program");
        if !any_change {
            break;
        }
    }

    // Remove all const functions - they should all have been specialized by now
    let const_func_names: Vec<_> = program
        .functions
        .iter()
        .filter(|(_, func)| func.has_const_arguments())
        .map(|(name, _)| name.clone())
        .collect();
    for name in const_func_names {
        program.functions.remove(&name);
    }

    let mut new_functions = BTreeMap::new();
    let mut counters = Counters::default();
    let mut const_malloc = ConstMalloc::default();
    let const_arrays = &program.const_arrays;
    for (name, func) in &program.functions {
        let mut array_manager = ArrayManager::default();
        let simplified_instructions = simplify_lines(
            &program.functions,
            func.file_id,
            func.n_returned_vars,
            &func.body,
            &mut counters,
            &mut new_functions,
            false,
            &mut array_manager,
            &mut const_malloc,
            const_arrays,
        );
        let arguments = func
            .arguments
            .iter()
            .map(|(v, is_const)| {
                assert!(!is_const,);
                v.clone()
            })
            .collect::<Vec<_>>();
        let simplified_function = SimpleFunction {
            name: name.clone(),
            file_id: func.file_id,
            arguments,
            n_returned_vars: func.n_returned_vars,
            instructions: simplified_instructions,
        };
        if !func.assume_always_returns {
            check_function_always_returns(&simplified_function);
        }
        new_functions.insert(name.clone(), simplified_function);
        const_malloc.map.clear();
    }
    SimpleProgram {
        functions: new_functions,
    }
}

fn unroll_loops_in_program(program: &mut Program, unroll_counter: &mut Counter) -> bool {
    let mut changed = false;
    for func in program.functions.values_mut() {
        changed |= unroll_loops_in_lines(&mut func.body, &program.const_arrays, unroll_counter);
    }
    changed
}

fn unroll_loops_in_lines(
    lines: &mut Vec<Line>,
    const_arrays: &BTreeMap<String, ConstArrayValue>,
    unroll_counter: &mut Counter,
) -> bool {
    let mut changed = false;
    let mut i = 0;
    while i < lines.len() {
        // First, recursively process nested structures
        match &mut lines[i] {
            Line::ForLoop { body, .. } => {
                changed |= unroll_loops_in_lines(body, const_arrays, unroll_counter);
            }
            Line::IfCondition {
                then_branch,
                else_branch,
                ..
            } => {
                changed |= unroll_loops_in_lines(then_branch, const_arrays, unroll_counter);
                changed |= unroll_loops_in_lines(else_branch, const_arrays, unroll_counter);
            }
            Line::Match { arms, .. } => {
                for (_, arm_body) in arms {
                    changed |= unroll_loops_in_lines(arm_body, const_arrays, unroll_counter);
                }
            }
            _ => {}
        }

        // Now try to unroll if it's an unrollable loop
        if let Line::ForLoop {
            iterator,
            start,
            end,
            body,
            rev,
            unroll: true,
            line_number: _,
        } = &lines[i]
            && let (Some(start_val), Some(end_val)) = (start.naive_eval(const_arrays), end.naive_eval(const_arrays))
        {
            let start_usize = start_val.to_usize();
            let end_usize = end_val.to_usize();
            let unroll_index = unroll_counter.next();

            let (internal_vars, _) = find_variable_usage(body, const_arrays);

            let mut range: Vec<_> = (start_usize..end_usize).collect();
            if *rev {
                range.reverse();
            }

            let iterator = iterator.clone();
            let body = body.clone();

            let mut unrolled = Vec::new();
            for j in range {
                let mut body_copy = body.clone();
                replace_vars_for_unroll(&mut body_copy, &iterator, unroll_index, j, &internal_vars);
                unrolled.extend(body_copy);
            }

            let num_inserted = unrolled.len();
            lines.splice(i..=i, unrolled);
            changed = true;
            i += num_inserted;
            continue;
        }

        i += 1;
    }
    changed
}

/// Analyzes a simplified function to verify that it returns on each code path.
fn check_function_always_returns(func: &SimpleFunction) {
    check_block_always_returns(&func.name, &func.instructions);
}

fn check_block_always_returns(function_name: &String, instructions: &[SimpleLine]) {
    match instructions.last() {
        Some(SimpleLine::Match { value: _, arms }) => {
            for arm in arms {
                check_block_always_returns(function_name, arm);
            }
        }
        Some(SimpleLine::IfNotZero {
            condition: _,
            then_branch,
            else_branch,
            line_number: _,
        }) => {
            check_block_always_returns(function_name, then_branch);
            check_block_always_returns(function_name, else_branch);
        }
        Some(SimpleLine::FunctionRet { return_data: _ }) => {
            // good
        }
        Some(SimpleLine::Panic) => {
            // good
        }
        _ => {
            panic!("Cannot prove that function always returns: {function_name}");
        }
    }
}

/// Analyzes the program to verify that each variable is defined in each context where it is used.
fn check_program_scoping(program: &Program) {
    for (_, function) in program.functions.iter() {
        let mut scope = Scope { vars: BTreeSet::new() };
        for (arg, _) in function.arguments.iter() {
            scope.vars.insert(arg.clone());
        }
        let mut ctx = Context {
            scopes: vec![scope],
            const_arrays: program.const_arrays.clone(),
        };

        check_block_scoping(&function.body, &mut ctx);
    }
}

/// Analyzes the block to verify that each variable is defined in each context where it is used.
fn check_block_scoping(block: &[Line], ctx: &mut Context) {
    for line in block.iter() {
        match line {
            Line::ForwardDeclaration { var } => {
                let last_scope = ctx.scopes.last_mut().unwrap();
                assert!(
                    !last_scope.vars.contains(var),
                    "Variable declared multiple times in the same scope: {var}",
                );
                last_scope.vars.insert(var.clone());
            }
            Line::Match { value, arms } => {
                check_expr_scoping(value, ctx);
                for (_, arm) in arms {
                    ctx.scopes.push(Scope { vars: BTreeSet::new() });
                    check_block_scoping(arm, ctx);
                    ctx.scopes.pop();
                }
            }
            Line::Assignment { var, value } => {
                check_expr_scoping(value, ctx);
                let last_scope = ctx.scopes.last_mut().unwrap();
                assert!(
                    !last_scope.vars.contains(var),
                    "Variable declared multiple times in the same scope: {var}",
                );
                last_scope.vars.insert(var.clone());
            }
            Line::ArrayAssign { array, index, value } => {
                check_simple_expr_scoping(array, ctx);
                check_expr_scoping(index, ctx);
                check_expr_scoping(value, ctx);
            }
            Line::Assert { boolean, .. } => {
                check_boolean_scoping(boolean, ctx);
            }
            Line::IfCondition {
                condition,
                then_branch,
                else_branch,
                line_number: _,
            } => {
                check_condition_scoping(condition, ctx);
                for branch in [then_branch, else_branch] {
                    ctx.scopes.push(Scope { vars: BTreeSet::new() });
                    check_block_scoping(branch, ctx);
                    ctx.scopes.pop();
                }
            }
            Line::ForLoop {
                iterator,
                start,
                end,
                body,
                rev: _,
                unroll: _,
                line_number: _,
            } => {
                check_expr_scoping(start, ctx);
                check_expr_scoping(end, ctx);
                let mut new_scope_vars = BTreeSet::new();
                new_scope_vars.insert(iterator.clone());
                ctx.scopes.push(Scope { vars: new_scope_vars });
                check_block_scoping(body, ctx);
                ctx.scopes.pop();
            }
            Line::FunctionCall {
                function_name: _,
                args,
                return_data,
                line_number: _,
            } => {
                for arg in args {
                    check_expr_scoping(arg, ctx);
                }
                let last_scope = ctx.scopes.last_mut().unwrap();
                for target in return_data {
                    match target {
                        AssignmentTarget::Var(var) => {
                            assert!(
                                !last_scope.vars.contains(var),
                                "Variable declared multiple times in the same scope: {var}",
                            );
                            last_scope.vars.insert(var.clone());
                        }
                        AssignmentTarget::ArrayAccess { .. } => {}
                    }
                }
                for target in return_data {
                    match target {
                        AssignmentTarget::Var(_) => {}
                        AssignmentTarget::ArrayAccess { array, index } => {
                            check_simple_expr_scoping(array, ctx);
                            check_expr_scoping(index, ctx);
                        }
                    }
                }
            }
            Line::FunctionRet { return_data } => {
                for expr in return_data {
                    check_expr_scoping(expr, ctx);
                }
            }
            Line::Precompile { table: _, args } => {
                for arg in args {
                    check_expr_scoping(arg, ctx);
                }
            }
            Line::Break | Line::Panic | Line::LocationReport { .. } => {}
            Line::Print { line_info: _, content } => {
                for expr in content {
                    check_expr_scoping(expr, ctx);
                }
            }
            Line::MAlloc { var, size } => {
                check_expr_scoping(size, ctx);
                let last_scope = ctx.scopes.last_mut().unwrap();
                assert!(
                    !last_scope.vars.contains(var),
                    "Variable declared multiple times in the same scope: {var}",
                );
                last_scope.vars.insert(var.clone());
            }
            Line::CustomHint(_, args) => {
                for arg in args {
                    check_expr_scoping(arg, ctx);
                }
            }
            Line::PrivateInputStart { result } => {
                let last_scope = ctx.scopes.last_mut().unwrap();
                assert!(
                    !last_scope.vars.contains(result),
                    "Variable declared multiple times in the same scope: {result}"
                );
                last_scope.vars.insert(result.clone());
            }
        }
    }
}

/// Analyzes the expression to verify that each variable is defined in the given context.
fn check_expr_scoping(expr: &Expression, ctx: &Context) {
    match expr {
        Expression::Value(simple_expr) => {
            check_simple_expr_scoping(simple_expr, ctx);
        }
        Expression::ArrayAccess { array, index } => {
            check_simple_expr_scoping(array, ctx);
            for idx in index {
                check_expr_scoping(idx, ctx);
            }
        }
        Expression::Binary {
            left,
            operation: _,
            right,
        } => {
            check_expr_scoping(left, ctx);
            check_expr_scoping(right, ctx);
        }
        Expression::MathExpr(_, args) => {
            for arg in args {
                check_expr_scoping(arg, ctx);
            }
        }
    }
}

/// Analyzes the simple expression to verify that each variable is defined in the given context.
fn check_simple_expr_scoping(expr: &SimpleExpr, ctx: &Context) {
    match expr {
        SimpleExpr::Var(v) => {
            assert!(ctx.defines(v), "Variable used but not defined: {v}");
        }
        SimpleExpr::Constant(_) => {}
        SimpleExpr::ConstMallocAccess { .. } => {}
    }
}

fn check_boolean_scoping(boolean: &BooleanExpr<Expression>, ctx: &Context) {
    check_expr_scoping(&boolean.left, ctx);
    check_expr_scoping(&boolean.right, ctx);
}

fn check_condition_scoping(condition: &Condition, ctx: &Context) {
    match condition {
        Condition::Expression(expr, _) => {
            check_expr_scoping(expr, ctx);
        }
        Condition::Comparison(boolean) => {
            check_boolean_scoping(boolean, ctx);
        }
    }
}

#[derive(Debug, Clone, Default)]
struct Counters {
    aux_vars: usize,
    loops: usize,
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
}

impl ArrayManager {
    fn get_aux_var(&mut self, array: &SimpleExpr, index: &Expression) -> Var {
        if let Some(var) = self.aux_vars.get(&(array.clone(), index.clone())) {
            return var.clone();
        }
        let new_var = format!("@arr_aux_{}", self.counter);
        self.counter += 1;
        self.aux_vars.insert((array.clone(), index.clone()), new_var.clone());
        new_var
    }
}

#[allow(clippy::too_many_arguments)]
fn simplify_lines(
    functions: &BTreeMap<String, Function>,
    file_id: FileId,
    n_returned_vars: usize,
    lines: &[Line],
    counters: &mut Counters,
    new_functions: &mut BTreeMap<String, SimpleFunction>,
    in_a_loop: bool,
    array_manager: &mut ArrayManager,
    const_malloc: &mut ConstMalloc,
    const_arrays: &BTreeMap<String, ConstArrayValue>,
) -> Vec<SimpleLine> {
    let mut res = Vec::new();
    for line in lines {
        match line {
            Line::ForwardDeclaration { var } => {
                res.push(SimpleLine::ForwardDeclaration { var: var.clone() });
            }
            Line::Match { value, arms } => {
                let simple_value = simplify_expr(value, &mut res, counters, array_manager, const_malloc, const_arrays);
                let mut simple_arms = vec![];
                for (i, (pattern, statements)) in arms.iter().enumerate() {
                    assert_eq!(*pattern, i, "match patterns should be consecutive, starting from 0");
                    simple_arms.push(simplify_lines(
                        functions,
                        file_id,
                        n_returned_vars,
                        statements,
                        counters,
                        new_functions,
                        in_a_loop,
                        array_manager,
                        const_malloc,
                        const_arrays,
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
                        const_arrays,
                    );
                }
                Expression::Binary { left, operation, right } => {
                    let left = simplify_expr(left, &mut res, counters, array_manager, const_malloc, const_arrays);
                    let right = simplify_expr(right, &mut res, counters, array_manager, const_malloc, const_arrays);
                    res.push(SimpleLine::Assignment {
                        var: var.clone().into(),
                        operation: *operation,
                        arg0: left,
                        arg1: right,
                    });
                }
                Expression::MathExpr(_, _) => unreachable!(),
            },
            Line::ArrayAssign { array, index, value } => {
                handle_array_assignment(
                    counters,
                    &mut res,
                    array.clone(),
                    &[index.clone()],
                    ArrayAccessType::ArrayIsAssigned(value.clone()),
                    array_manager,
                    const_malloc,
                    const_arrays,
                );
            }
            Line::Assert {
                boolean,
                line_number,
                debug,
            } => {
                let left = simplify_expr(
                    &boolean.left,
                    &mut res,
                    counters,
                    array_manager,
                    const_malloc,
                    const_arrays,
                );
                let right = simplify_expr(
                    &boolean.right,
                    &mut res,
                    counters,
                    array_manager,
                    const_malloc,
                    const_arrays,
                );

                if *debug {
                    res.push(SimpleLine::DebugAssert(
                        BooleanExpr {
                            left,
                            right,
                            kind: boolean.kind,
                        },
                        *line_number,
                    ));
                } else {
                    match boolean.kind {
                        Boolean::Different => {
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
                                line_number: *line_number,
                            });
                        }
                        Boolean::Equal => {
                            let (var, other) = if let Ok(left) = left.clone().try_into() {
                                (left, right)
                            } else if let Ok(right) = right.clone().try_into() {
                                (right, left)
                            } else {
                                // Both are constants - evaluate at compile time
                                if let (SimpleExpr::Constant(left_const), SimpleExpr::Constant(right_const)) =
                                    (&left, &right)
                                {
                                    if let (Some(left_val), Some(right_val)) =
                                        (left_const.naive_eval(), right_const.naive_eval())
                                    {
                                        if left_val == right_val {
                                            // Assertion passes at compile time, no code needed
                                            continue;
                                        } else {
                                            panic!(
                                                "Compile-time assertion failed: {} != {} (lines {})",
                                                left_val.to_usize(),
                                                right_val.to_usize(),
                                                line_number
                                            );
                                        }
                                    }
                                }
                                panic!("Unsupported equality assertion: {left:?}, {right:?}")
                            };
                            res.push(SimpleLine::Assignment {
                                var,
                                operation: HighLevelOperation::Add,
                                arg0: other,
                                arg1: SimpleExpr::zero(),
                            });
                        }
                        Boolean::LessThan => unreachable!(),
                    }
                }
            }
            Line::IfCondition {
                condition,
                then_branch,
                else_branch,
                line_number,
            } => {
                let (condition_simplified, then_branch, else_branch) = match condition {
                    Condition::Comparison(condition) => {
                        // Transform if a == b then X else Y into if a != b then Y else X

                        let (left, right, then_branch, else_branch) = match condition.kind {
                            Boolean::Equal => (&condition.left, &condition.right, else_branch, then_branch), // switched
                            Boolean::Different => (&condition.left, &condition.right, then_branch, else_branch),
                            Boolean::LessThan => unreachable!(),
                        };

                        let left_simplified =
                            simplify_expr(left, &mut res, counters, array_manager, const_malloc, const_arrays);
                        let right_simplified =
                            simplify_expr(right, &mut res, counters, array_manager, const_malloc, const_arrays);

                        let diff_var = format!("@diff_{}", counters.aux_vars);
                        counters.aux_vars += 1;
                        res.push(SimpleLine::Assignment {
                            var: diff_var.clone().into(),
                            operation: HighLevelOperation::Sub,
                            arg0: left_simplified,
                            arg1: right_simplified,
                        });
                        (diff_var.into(), then_branch, else_branch)
                    }
                    Condition::Expression(condition, assume_boolean) => {
                        let condition_simplified =
                            simplify_expr(condition, &mut res, counters, array_manager, const_malloc, const_arrays);

                        match assume_boolean {
                            AssumeBoolean::AssumeBoolean => {}
                            AssumeBoolean::DoNotAssumeBoolean => {
                                // Check condition_simplified is boolean
                                let one_minus_condition_var = format!("@aux_{}", counters.aux_vars);
                                counters.aux_vars += 1;
                                res.push(SimpleLine::Assignment {
                                    var: one_minus_condition_var.clone().into(),
                                    operation: HighLevelOperation::Sub,
                                    arg0: SimpleExpr::Constant(ConstExpression::Value(ConstantValue::Scalar(1))),
                                    arg1: condition_simplified.clone(),
                                });
                                res.push(SimpleLine::TestZero {
                                    operation: HighLevelOperation::Mul,
                                    arg0: condition_simplified.clone(),
                                    arg1: one_minus_condition_var.into(),
                                });
                            }
                        }

                        (condition_simplified, then_branch, else_branch)
                    }
                };

                let mut array_manager_then = array_manager.clone();
                let then_branch_simplified = simplify_lines(
                    functions,
                    file_id,
                    n_returned_vars,
                    then_branch,
                    counters,
                    new_functions,
                    in_a_loop,
                    &mut array_manager_then,
                    const_malloc,
                    const_arrays,
                );
                let mut array_manager_else = array_manager_then.clone();
                array_manager_else.valid = array_manager.valid.clone(); // Crucial: remove the access added in the IF branch

                let else_branch_simplified = simplify_lines(
                    functions,
                    file_id,
                    n_returned_vars,
                    else_branch,
                    counters,
                    new_functions,
                    in_a_loop,
                    &mut array_manager_else,
                    const_malloc,
                    const_arrays,
                );

                *array_manager = array_manager_else.clone();
                // keep the intersection both branches
                array_manager.valid = array_manager
                    .valid
                    .intersection(&array_manager_then.valid)
                    .cloned()
                    .collect();

                res.push(SimpleLine::IfNotZero {
                    condition: condition_simplified,
                    then_branch: then_branch_simplified,
                    else_branch: else_branch_simplified,
                    line_number: *line_number,
                });
            }
            Line::ForLoop {
                iterator,
                start,
                end,
                body,
                rev,
                unroll,
                line_number,
            } => {
                assert!(!*unroll, "Unrolled loops should have been handled already");

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
                    functions,
                    file_id,
                    0,
                    body,
                    counters,
                    new_functions,
                    true,
                    array_manager,
                    &mut loop_const_malloc,
                    const_arrays,
                );
                const_malloc.counter = loop_const_malloc.counter;
                array_manager.valid = valid_aux_vars_in_array_manager_before; // restore the valid aux vars

                let func_name = format!("@loop_{}_line_{}", counters.loops, line_number);
                counters.loops += 1;

                // Find variables used inside loop but defined outside
                let (_, mut external_vars) = find_variable_usage(body, const_arrays);

                // Include variables in start/end
                for expr in [start, end] {
                    for var in vars_in_expression(expr, const_arrays) {
                        external_vars.insert(var);
                    }
                }
                external_vars.remove(iterator); // Iterator is internal to loop

                let mut external_vars: Vec<_> = external_vars.into_iter().collect();

                let start_simplified =
                    simplify_expr(start, &mut res, counters, array_manager, const_malloc, const_arrays);
                let mut end_simplified =
                    simplify_expr(end, &mut res, counters, array_manager, const_malloc, const_arrays);
                if let SimpleExpr::ConstMallocAccess { malloc_label, offset } = end_simplified.clone() {
                    // we use an auxilary variable to store the end value (const malloc inside non-unrolled loops does not work)
                    let aux_end_var = format!("@aux_end_{}", counters.aux_vars);
                    counters.aux_vars += 1;
                    res.push(SimpleLine::Assignment {
                        var: aux_end_var.clone().into(),
                        operation: HighLevelOperation::Add,
                        arg0: SimpleExpr::ConstMallocAccess { malloc_label, offset },
                        arg1: SimpleExpr::zero(),
                    });
                    end_simplified = SimpleExpr::Var(aux_end_var);
                }

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
                    SourceLocation {
                        line_number: *line_number,
                        file_id,
                    },
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
                    line_number: *line_number,
                });
            }
            Line::FunctionCall {
                function_name,
                args,
                return_data,
                line_number,
            } => {
                let function = functions
                    .get(function_name)
                    .unwrap_or_else(|| panic!("Function used but not defined: {function_name}, at line {line_number}"));
                if return_data.len() != function.n_returned_vars {
                    panic!(
                        "Expected {} returned vars (and not {}) in call to {function_name}, at line {line_number}",
                        function.n_returned_vars,
                        return_data.len()
                    );
                }
                if args.len() != function.arguments.len() {
                    panic!(
                        "Expected {} arguments (and not {}) in call to {function_name}, at line {line_number}",
                        function.arguments.len(),
                        args.len()
                    );
                }

                let simplified_args = args
                    .iter()
                    .map(|arg| simplify_expr(arg, &mut res, counters, array_manager, const_malloc, const_arrays))
                    .collect::<Vec<_>>();

                // Generate temp vars for all return values and track array targets
                let mut temp_vars = Vec::new();
                let mut array_targets: Vec<(usize, SimpleExpr, Box<Expression>)> = Vec::new();

                for (i, target) in return_data.iter().enumerate() {
                    match target {
                        AssignmentTarget::Var(var) => {
                            temp_vars.push(var.clone());
                        }
                        AssignmentTarget::ArrayAccess { array, index } => {
                            let temp_var = format!("@ret_temp_{}", counters.aux_vars);
                            counters.aux_vars += 1;
                            temp_vars.push(temp_var);
                            array_targets.push((i, array.clone(), index.clone()));
                        }
                    }
                }

                res.push(SimpleLine::FunctionCall {
                    function_name: function_name.clone(),
                    args: simplified_args,
                    return_data: temp_vars.clone(),
                    line_number: *line_number,
                });

                // For array access targets, add DEREF instructions to copy temp to array element
                for (i, array, index) in array_targets {
                    handle_array_assignment(
                        counters,
                        &mut res,
                        array,
                        &[*index],
                        ArrayAccessType::ArrayIsAssigned(Expression::Value(SimpleExpr::Var(temp_vars[i].clone()))),
                        array_manager,
                        const_malloc,
                        const_arrays,
                    );
                }
            }
            Line::FunctionRet { return_data } => {
                assert!(!in_a_loop, "Function return inside a loop is not currently supported");
                assert!(
                    return_data.len() == n_returned_vars,
                    "Wrong number of return values in return statement; expected {n_returned_vars} but got {}",
                    return_data.len()
                );
                let simplified_return_data = return_data
                    .iter()
                    .map(|ret| simplify_expr(ret, &mut res, counters, array_manager, const_malloc, const_arrays))
                    .collect::<Vec<_>>();
                res.push(SimpleLine::FunctionRet {
                    return_data: simplified_return_data,
                });
            }
            Line::Precompile { table, args } => {
                let simplified_args = args
                    .iter()
                    .map(|arg| simplify_expr(arg, &mut res, counters, array_manager, const_malloc, const_arrays))
                    .collect::<Vec<_>>();
                res.push(SimpleLine::Precompile {
                    table: *table,
                    args: simplified_args,
                });
            }
            Line::Print { line_info, content } => {
                let simplified_content = content
                    .iter()
                    .map(|var| simplify_expr(var, &mut res, counters, array_manager, const_malloc, const_arrays))
                    .collect::<Vec<_>>();
                res.push(SimpleLine::Print {
                    line_info: line_info.clone(),
                    content: simplified_content,
                });
            }
            Line::Break => {
                assert!(in_a_loop, "Break statement outside of a loop");
                res.push(SimpleLine::FunctionRet { return_data: vec![] });
            }
            Line::MAlloc { var, size } => {
                let simplified_size =
                    simplify_expr(size, &mut res, counters, array_manager, const_malloc, const_arrays);
                match simplified_size {
                    SimpleExpr::Constant(const_size) => {
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
                        });
                    }
                }
            }
            Line::PrivateInputStart { result } => {
                res.push(SimpleLine::PrivateInputStart { result: result.clone() });
            }
            Line::CustomHint(hint, args) => {
                let simplified_args = args
                    .iter()
                    .map(|expr| simplify_expr(expr, &mut res, counters, array_manager, const_malloc, const_arrays))
                    .collect::<Vec<_>>();
                res.push(SimpleLine::CustomHint(*hint, simplified_args));
            }
            Line::Panic => {
                res.push(SimpleLine::Panic);
            }
            Line::LocationReport { location } => {
                res.push(SimpleLine::LocationReport {
                    location: SourceLocation {
                        line_number: *location,
                        file_id,
                    },
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
    const_arrays: &BTreeMap<String, ConstArrayValue>,
) -> SimpleExpr {
    match expr {
        Expression::Value(value) => value.simplify_if_const(),
        Expression::ArrayAccess { array, index } => {
            // Check for const array access
            if let SimpleExpr::Var(array_var) = array
                && let Some(arr) = const_arrays.get(array_var)
            {
                let simplified_index = index
                    .iter()
                    .map(|idx| {
                        simplify_expr(idx, lines, counters, array_manager, const_malloc, const_arrays)
                            .as_constant()
                            .expect("Const array access index should be constant")
                            .naive_eval()
                            .expect("Const array access index should be constant")
                            .to_usize()
                    })
                    .collect::<Vec<_>>();

                return SimpleExpr::Constant(ConstExpression::from(
                    arr.navigate(&simplified_index)
                        .expect("Const array access index out of bounds")
                        .as_scalar()
                        .expect("Const array access should return a scalar"),
                ));
            }

            assert_eq!(index.len(), 1);
            let index = index[0].clone();

            if let SimpleExpr::Var(array_var) = array
                && let Some(label) = const_malloc.map.get(array_var)
                && let Ok(mut offset) = ConstExpression::try_from(index.clone())
            {
                offset = offset.try_naive_simplification();
                return SimpleExpr::ConstMallocAccess {
                    malloc_label: *label,
                    offset,
                };
            }

            let aux_arr = array_manager.get_aux_var(array, &index); // auxiliary var to store m[array + index]

            if !array_manager.valid.insert(aux_arr.clone()) {
                return SimpleExpr::Var(aux_arr);
            }

            handle_array_assignment(
                counters,
                lines,
                array.clone(),
                &[index],
                ArrayAccessType::VarIsAssigned(aux_arr.clone()),
                array_manager,
                const_malloc,
                const_arrays,
            );
            SimpleExpr::Var(aux_arr)
        }
        Expression::Binary { left, operation, right } => {
            let left_var = simplify_expr(left, lines, counters, array_manager, const_malloc, const_arrays);
            let right_var = simplify_expr(right, lines, counters, array_manager, const_malloc, const_arrays);

            if let (SimpleExpr::Constant(left_cst), SimpleExpr::Constant(right_cst)) = (&left_var, &right_var) {
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
        Expression::MathExpr(formula, args) => {
            let simplified_args = args
                .iter()
                .map(|arg| {
                    simplify_expr(arg, lines, counters, array_manager, const_malloc, const_arrays)
                        .as_constant()
                        .unwrap()
                })
                .collect::<Vec<_>>();
            SimpleExpr::Constant(ConstExpression::MathExpr(*formula, simplified_args))
        }
    }
}

/// Returns (internal_vars, external_vars)
pub fn find_variable_usage(
    lines: &[Line],
    const_arrays: &BTreeMap<String, ConstArrayValue>,
) -> (BTreeSet<Var>, BTreeSet<Var>) {
    let mut internal_vars = BTreeSet::new();
    let mut external_vars = BTreeSet::new();

    let on_new_expr = |expr: &Expression, internal_vars: &BTreeSet<Var>, external_vars: &mut BTreeSet<Var>| {
        for var in vars_in_expression(expr, const_arrays) {
            if !internal_vars.contains(&var) && !const_arrays.contains_key(&var) {
                external_vars.insert(var);
            }
        }
    };

    let on_new_condition =
        |condition: &Condition, internal_vars: &BTreeSet<Var>, external_vars: &mut BTreeSet<Var>| match condition {
            Condition::Comparison(comp) => {
                on_new_expr(&comp.left, internal_vars, external_vars);
                on_new_expr(&comp.right, internal_vars, external_vars);
            }
            Condition::Expression(expr, _assume_boolean) => {
                on_new_expr(expr, internal_vars, external_vars);
            }
        };

    for line in lines {
        match line {
            Line::ForwardDeclaration { var } => {
                internal_vars.insert(var.clone());
            }
            Line::Match { value, arms } => {
                on_new_expr(value, &internal_vars, &mut external_vars);
                for (_, statements) in arms {
                    let (stmt_internal, stmt_external) = find_variable_usage(statements, const_arrays);
                    internal_vars.extend(stmt_internal);
                    external_vars.extend(stmt_external.into_iter().filter(|v| !internal_vars.contains(v)));
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
                line_number: _,
            } => {
                on_new_condition(condition, &internal_vars, &mut external_vars);

                let (then_internal, then_external) = find_variable_usage(then_branch, const_arrays);
                let (else_internal, else_external) = find_variable_usage(else_branch, const_arrays);

                internal_vars.extend(then_internal.union(&else_internal).cloned());
                external_vars.extend(
                    then_external
                        .union(&else_external)
                        .filter(|v| !internal_vars.contains(*v))
                        .cloned(),
                );
            }
            Line::FunctionCall { args, return_data, .. } => {
                for arg in args {
                    on_new_expr(arg, &internal_vars, &mut external_vars);
                }
                for target in return_data {
                    match target {
                        AssignmentTarget::Var(var) => {
                            internal_vars.insert(var.clone());
                        }
                        AssignmentTarget::ArrayAccess { array, index } => {
                            if let SimpleExpr::Var(var) = array {
                                assert!(!const_arrays.contains_key(var), "Cannot assign to const array");
                                if !internal_vars.contains(var) {
                                    external_vars.insert(var.clone());
                                }
                            }
                            on_new_expr(index, &internal_vars, &mut external_vars);
                        }
                    }
                }
            }
            Line::Assert { boolean, .. } => {
                on_new_condition(
                    &Condition::Comparison(boolean.clone()),
                    &internal_vars,
                    &mut external_vars,
                );
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
            Line::Precompile { table: _, args } => {
                for arg in args {
                    on_new_expr(arg, &internal_vars, &mut external_vars);
                }
            }
            Line::Print { content, .. } => {
                for var in content {
                    on_new_expr(var, &internal_vars, &mut external_vars);
                }
            }
            Line::PrivateInputStart { result } => {
                internal_vars.insert(result.clone());
            }
            Line::CustomHint(_, args) => {
                for expr in args {
                    on_new_expr(expr, &internal_vars, &mut external_vars);
                }
            }
            Line::ForLoop {
                iterator,
                start,
                end,
                body,
                rev: _,
                unroll: _,
                line_number: _,
            } => {
                let (body_internal, body_external) = find_variable_usage(body, const_arrays);
                internal_vars.extend(body_internal);
                internal_vars.insert(iterator.clone());
                external_vars.extend(body_external.difference(&internal_vars).cloned());
                on_new_expr(start, &internal_vars, &mut external_vars);
                on_new_expr(end, &internal_vars, &mut external_vars);
            }
            Line::ArrayAssign { array, index, value } => {
                on_new_expr(&array.clone().into(), &internal_vars, &mut external_vars);
                on_new_expr(index, &internal_vars, &mut external_vars);
                on_new_expr(value, &internal_vars, &mut external_vars);
            }
            Line::Panic | Line::Break | Line::LocationReport { .. } => {}
        }
    }

    (internal_vars, external_vars)
}

fn inline_simple_expr(simple_expr: &mut SimpleExpr, args: &BTreeMap<Var, SimpleExpr>, inlining_count: usize) {
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
            for idx in index {
                inline_expr(idx, args, inlining_count);
            }
        }
        Expression::Binary { left, right, .. } => {
            inline_expr(left, args, inlining_count);
            inline_expr(right, args, inlining_count);
        }
        Expression::MathExpr(_, math_args) => {
            for arg in math_args {
                inline_expr(arg, args, inlining_count);
            }
        }
    }
}

fn inline_lines(
    lines: &mut Vec<Line>,
    args: &BTreeMap<Var, SimpleExpr>,
    res: &[AssignmentTarget],
    inlining_count: usize,
) {
    let inline_comparison = |comparison: &mut BooleanExpr<Expression>| {
        inline_expr(&mut comparison.left, args, inlining_count);
        inline_expr(&mut comparison.right, args, inlining_count);
    };

    let inline_condition = |condition: &mut Condition| match condition {
        Condition::Comparison(comparison) => inline_comparison(comparison),
        Condition::Expression(expr, _assume_boolean) => inline_expr(expr, args, inlining_count),
    };

    let inline_internal_var = |var: &mut Var| {
        assert!(
            !args.contains_key(var),
            "Variable {var} is both an argument and declared in the inlined function"
        );
        *var = format!("@inlined_var_{inlining_count}_{var}");
    };

    let mut lines_to_replace = vec![];
    for (i, line) in lines.iter_mut().enumerate() {
        match line {
            Line::ForwardDeclaration { var } => {
                inline_internal_var(var);
            }
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
                line_number: _,
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
                for target in return_data {
                    match target {
                        AssignmentTarget::Var(var) => {
                            inline_internal_var(var);
                        }
                        AssignmentTarget::ArrayAccess { array, index } => {
                            inline_simple_expr(array, args, inlining_count);
                            inline_expr(index, args, inlining_count);
                        }
                    }
                }
            }
            Line::Assert { boolean, .. } => {
                inline_comparison(boolean);
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
                        .map(|(target, expr)| match target {
                            AssignmentTarget::Var(res_var) => Line::Assignment {
                                var: res_var.clone(),
                                value: expr.clone(),
                            },
                            AssignmentTarget::ArrayAccess { array, index } => Line::ArrayAssign {
                                array: array.clone(),
                                index: (**index).clone(),
                                value: expr.clone(),
                            },
                        })
                        .collect::<Vec<_>>(),
                ));
            }
            Line::MAlloc { var, size, .. } => {
                inline_expr(size, args, inlining_count);
                inline_internal_var(var);
            }
            Line::Precompile {
                table: _,
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
            Line::CustomHint(_, decomposed_args) => {
                for expr in decomposed_args {
                    inline_expr(expr, args, inlining_count);
                }
            }
            Line::PrivateInputStart { result } => {
                inline_internal_var(result);
            }
            Line::ForLoop {
                iterator,
                start,
                end,
                body,
                rev: _,
                unroll: _,
                line_number: _,
            } => {
                inline_lines(body, args, res, inlining_count);
                inline_internal_var(iterator);
                inline_expr(start, args, inlining_count);
                inline_expr(end, args, inlining_count);
            }
            Line::ArrayAssign { array, index, value } => {
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

fn vars_in_expression(expr: &Expression, const_arrays: &BTreeMap<String, ConstArrayValue>) -> BTreeSet<Var> {
    let mut vars = BTreeSet::new();
    match expr {
        Expression::Value(value) => {
            if let SimpleExpr::Var(var) = value {
                vars.insert(var.clone());
            }
        }
        Expression::ArrayAccess { array, index } => {
            if let SimpleExpr::Var(array) = array
                && !const_arrays.contains_key(array)
            {
                vars.insert(array.clone());
            }
            for idx in index {
                vars.extend(vars_in_expression(idx, const_arrays));
            }
        }
        Expression::Binary { left, right, .. } => {
            vars.extend(vars_in_expression(left, const_arrays));
            vars.extend(vars_in_expression(right, const_arrays));
        }
        Expression::MathExpr(_, args) => {
            for arg in args {
                vars.extend(vars_in_expression(arg, const_arrays));
            }
        }
    }
    vars
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ArrayAccessType {
    VarIsAssigned(Var),          // var = array[index]
    ArrayIsAssigned(Expression), // array[index] = expr
}

#[allow(clippy::too_many_arguments)]
fn handle_array_assignment(
    counters: &mut Counters,
    res: &mut Vec<SimpleLine>,
    array: SimpleExpr,
    index: &[Expression],
    access_type: ArrayAccessType,
    array_manager: &mut ArrayManager,
    const_malloc: &ConstMalloc,
    const_arrays: &BTreeMap<String, ConstArrayValue>,
) {
    let simplified_index = index
        .iter()
        .map(|idx| simplify_expr(idx, res, counters, array_manager, const_malloc, const_arrays))
        .collect::<Vec<_>>();

    if let (ArrayAccessType::VarIsAssigned(var), SimpleExpr::Var(array_var)) = (&access_type, &array) {
        if let Some(const_array) = const_arrays.get(array_var) {
            let idx = simplified_index
                .iter()
                .map(|idx| {
                    idx.as_constant()
                        .expect("Const array access index should be constant")
                        .naive_eval()
                        .unwrap()
                        .to_usize()
                })
                .collect::<Vec<_>>();
            let value = const_array
                .navigate(&idx)
                .expect("Const array access index out of bounds")
                .as_scalar()
                .expect("Const array access should return a scalar");
            res.push(SimpleLine::Assignment {
                var: var.clone().into(),
                operation: HighLevelOperation::Add,
                arg0: SimpleExpr::Constant(ConstExpression::from(value)),
                arg1: SimpleExpr::zero(),
            });
            return;
        }
    }

    if simplified_index.len() == 1
        && let SimpleExpr::Constant(offset) = simplified_index[0].clone()
        && let SimpleExpr::Var(array_var) = &array
        && let Some(label) = const_malloc.map.get(array_var)
        && let ArrayAccessType::ArrayIsAssigned(Expression::Binary { left, operation, right }) = &access_type
    {
        let arg0 = simplify_expr(left, res, counters, array_manager, const_malloc, const_arrays);
        let arg1 = simplify_expr(right, res, counters, array_manager, const_malloc, const_arrays);
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
            simplify_expr(&expr, res, counters, array_manager, const_malloc, const_arrays)
        }
    };

    // TODO opti: in some case we could use ConstMallocAccess
    assert_eq!(simplified_index.len(), 1);
    let simplified_index = simplified_index[0].clone();
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
    location: SourceLocation,
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
        line_number: location.line_number,
    });
    body.push(SimpleLine::FunctionRet { return_data: vec![] });

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
            else_branch: vec![SimpleLine::FunctionRet { return_data: vec![] }],
            line_number: location.line_number,
        },
    ];

    SimpleFunction {
        name,
        file_id: location.file_id,
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
            for index in index {
                replace_vars_for_unroll_in_expr(index, iterator, unroll_index, iterator_value, internal_vars);
            }
        }
        Expression::Binary { left, right, .. } => {
            replace_vars_for_unroll_in_expr(left, iterator, unroll_index, iterator_value, internal_vars);
            replace_vars_for_unroll_in_expr(right, iterator, unroll_index, iterator_value, internal_vars);
        }
        Expression::MathExpr(_, args) => {
            for arg in args {
                replace_vars_for_unroll_in_expr(arg, iterator, unroll_index, iterator_value, internal_vars);
            }
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
                replace_vars_for_unroll_in_expr(value, iterator, unroll_index, iterator_value, internal_vars);
                for (_, statements) in arms {
                    replace_vars_for_unroll(statements, iterator, unroll_index, iterator_value, internal_vars);
                }
            }
            Line::ForwardDeclaration { var } => {
                *var = format!("@unrolled_{unroll_index}_{iterator_value}_{var}");
            }
            Line::Assignment { var, value } => {
                assert!(var != iterator, "Weird");
                *var = format!("@unrolled_{unroll_index}_{iterator_value}_{var}");
                replace_vars_for_unroll_in_expr(value, iterator, unroll_index, iterator_value, internal_vars);
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
                        *array_var = format!("@unrolled_{unroll_index}_{iterator_value}_{array_var}");
                    }
                }
                replace_vars_for_unroll_in_expr(index, iterator, unroll_index, iterator_value, internal_vars);
                replace_vars_for_unroll_in_expr(value, iterator, unroll_index, iterator_value, internal_vars);
            }
            Line::Assert { boolean, .. } => {
                replace_vars_for_unroll_in_expr(
                    &mut boolean.left,
                    iterator,
                    unroll_index,
                    iterator_value,
                    internal_vars,
                );
                replace_vars_for_unroll_in_expr(
                    &mut boolean.right,
                    iterator,
                    unroll_index,
                    iterator_value,
                    internal_vars,
                );
            }
            Line::IfCondition {
                condition,
                then_branch,
                else_branch,
                line_number: _,
            } => {
                match condition {
                    Condition::Comparison(cond) => {
                        replace_vars_for_unroll_in_expr(
                            &mut cond.left,
                            iterator,
                            unroll_index,
                            iterator_value,
                            internal_vars,
                        );
                        replace_vars_for_unroll_in_expr(
                            &mut cond.right,
                            iterator,
                            unroll_index,
                            iterator_value,
                            internal_vars,
                        );
                    }
                    Condition::Expression(expr, _assume_bool) => {
                        replace_vars_for_unroll_in_expr(expr, iterator, unroll_index, iterator_value, internal_vars);
                    }
                }

                replace_vars_for_unroll(then_branch, iterator, unroll_index, iterator_value, internal_vars);
                replace_vars_for_unroll(else_branch, iterator, unroll_index, iterator_value, internal_vars);
            }
            Line::ForLoop {
                iterator: other_iterator,
                start,
                end,
                body,
                rev: _,
                unroll: _,
                line_number: _,
            } => {
                assert!(other_iterator != iterator);
                *other_iterator = format!("@unrolled_{unroll_index}_{iterator_value}_{other_iterator}");
                replace_vars_for_unroll_in_expr(start, iterator, unroll_index, iterator_value, internal_vars);
                replace_vars_for_unroll_in_expr(end, iterator, unroll_index, iterator_value, internal_vars);
                replace_vars_for_unroll(body, iterator, unroll_index, iterator_value, internal_vars);
            }
            Line::FunctionCall {
                function_name: _,
                args,
                return_data,
                line_number: _,
            } => {
                for arg in args {
                    replace_vars_for_unroll_in_expr(arg, iterator, unroll_index, iterator_value, internal_vars);
                }
                for target in return_data {
                    match target {
                        AssignmentTarget::Var(ret) => {
                            *ret = format!("@unrolled_{unroll_index}_{iterator_value}_{ret}");
                        }
                        AssignmentTarget::ArrayAccess { array, index } => {
                            if let SimpleExpr::Var(array_var) = array
                                && internal_vars.contains(array_var)
                            {
                                *array_var = format!("@unrolled_{unroll_index}_{iterator_value}_{array_var}");
                            }
                            replace_vars_for_unroll_in_expr(
                                index,
                                iterator,
                                unroll_index,
                                iterator_value,
                                internal_vars,
                            );
                        }
                    }
                }
            }
            Line::FunctionRet { return_data } => {
                for ret in return_data {
                    replace_vars_for_unroll_in_expr(ret, iterator, unroll_index, iterator_value, internal_vars);
                }
            }
            Line::Precompile { table: _, args } => {
                for arg in args {
                    replace_vars_for_unroll_in_expr(arg, iterator, unroll_index, iterator_value, internal_vars);
                }
            }
            Line::Print { line_info, content } => {
                // Print statements are not unrolled, so we don't need to change them
                *line_info += &format!(" (unrolled {unroll_index} {iterator_value})");
                for var in content {
                    replace_vars_for_unroll_in_expr(var, iterator, unroll_index, iterator_value, internal_vars);
                }
            }
            Line::MAlloc { var, size } => {
                assert!(var != iterator, "Weird");
                *var = format!("@unrolled_{unroll_index}_{iterator_value}_{var}");
                replace_vars_for_unroll_in_expr(size, iterator, unroll_index, iterator_value, internal_vars);
            }
            Line::PrivateInputStart { result } => {
                assert!(result != iterator, "Weird");
                *result = format!("@unrolled_{unroll_index}_{iterator_value}_{result}");
            }
            Line::CustomHint(_, decomposed_args) => {
                for expr in decomposed_args {
                    replace_vars_for_unroll_in_expr(expr, iterator, unroll_index, iterator_value, internal_vars);
                }
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

                handle_inlined_functions_helper(&mut func.body, &inlined_functions, &mut counter1, &mut counter2);

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

                handle_inlined_functions_helper(&mut func.body, &inlined_functions, &mut counter1, &mut counter2);

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

    assert!(max_iterations > 0, "Too many iterations processing inline functions");

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
                line_number: _,
            } => {
                if let Some(func) = inlined_functions.get(&*function_name) {
                    let mut inlined_lines = vec![];

                    // Only add forward declarations for variable targets, not array accesses
                    for target in return_data.iter() {
                        if let AssignmentTarget::Var(var) = target {
                            inlined_lines.push(Line::ForwardDeclaration { var: var.clone() });
                        }
                    }

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
                    inline_lines(&mut func_body, &inlined_args, return_data, total_inlined_counter.next());
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
            Line::ForLoop { body, unroll: _, .. } => {
                handle_inlined_functions_helper(body, inlined_functions, inlined_var_counter, total_inlined_counter);
            }
            Line::Match { arms, .. } => {
                for (_, arm) in arms {
                    handle_inlined_functions_helper(arm, inlined_functions, inlined_var_counter, total_inlined_counter);
                }
            }
            _ => {}
        }
    }
}

fn handle_const_arguments(program: &mut Program) -> bool {
    let mut any_changes = false;
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
            any_changes |= handle_const_arguments_helper(
                func.file_id,
                &mut func.body,
                &constant_functions,
                &mut new_functions,
                &program.const_arrays,
            );
        }
    }

    // Process newly created functions recursively until no more changes
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
                    func.file_id,
                    &mut func.body,
                    &constant_functions,
                    &mut additional_functions,
                    &program.const_arrays,
                );
                if additional_functions.len() > initial_count {
                    changed = true;
                    any_changes = true;
                }
            }
        }

        // Add any newly discovered functions
        for (name, func) in additional_functions {
            if let std::collections::btree_map::Entry::Vacant(e) = new_functions.entry(name) {
                e.insert(func);
                changed = true;
                any_changes = true;
            }
        }
    }

    any_changes |= !new_functions.is_empty();

    for (name, func) in new_functions {
        assert!(!program.functions.contains_key(&name));
        program.functions.insert(name, func);
    }

    // DON'T remove const functions here - they might be needed in subsequent iterations
    // They will be removed at the end of simplify_program

    any_changes
}

fn handle_const_arguments_helper(
    file_id: FileId,
    lines: &mut [Line],
    constant_functions: &BTreeMap<String, Function>,
    new_functions: &mut BTreeMap<String, Function>,
    const_arrays: &BTreeMap<String, ConstArrayValue>,
) -> bool {
    let mut changed = false;
    'outer: for line in lines {
        match line {
            Line::FunctionCall {
                function_name,
                args,
                return_data: _,
                line_number: _,
            } => {
                if let Some(func) = constant_functions.get(function_name) {
                    // Check if all const arguments can be evaluated
                    let mut const_evals = Vec::new();
                    for (arg_expr, (arg_var, is_constant)) in args.iter().zip(&func.arguments) {
                        if *is_constant {
                            if let Some(const_eval) = arg_expr.naive_eval(const_arrays) {
                                const_evals.push((arg_var.clone(), const_eval));
                            } else {
                                // Skip this call, will be handled in a later pass after more unrolling
                                continue 'outer;
                            }
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

                    changed = true;

                    if new_functions.contains_key(&const_funct_name) {
                        continue;
                    }

                    let mut new_body = func.body.clone();
                    replace_vars_by_const_in_lines(&mut new_body, &const_evals.iter().cloned().collect());
                    new_functions.insert(
                        const_funct_name.clone(),
                        Function {
                            name: const_funct_name,
                            file_id,
                            arguments: func
                                .arguments
                                .iter()
                                .filter(|(_, is_const)| !is_const)
                                .cloned()
                                .collect(),
                            inlined: false,
                            body: new_body,
                            n_returned_vars: func.n_returned_vars,
                            assume_always_returns: func.assume_always_returns,
                        },
                    );
                }
            }
            Line::IfCondition {
                then_branch,
                else_branch,
                ..
            } => {
                changed |= handle_const_arguments_helper(
                    file_id,
                    then_branch,
                    constant_functions,
                    new_functions,
                    const_arrays,
                );
                changed |= handle_const_arguments_helper(
                    file_id,
                    else_branch,
                    constant_functions,
                    new_functions,
                    const_arrays,
                );
            }
            Line::ForLoop { body, unroll: _, .. } => {
                // TODO we should unroll before const arguments handling
                handle_const_arguments_helper(file_id, body, constant_functions, new_functions, const_arrays);
            }
            Line::Match { arms, .. } => {
                for (_, arm) in arms {
                    changed |=
                        handle_const_arguments_helper(file_id, arm, constant_functions, new_functions, const_arrays);
                }
            }
            _ => {}
        }
    }
    changed
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
                assert!(!map.contains_key(array_var), "Array {array_var} is a constant");
            }
            for index in index {
                replace_vars_by_const_in_expr(index, map);
            }
        }
        Expression::Binary { left, right, .. } => {
            replace_vars_by_const_in_expr(left, map);
            replace_vars_by_const_in_expr(right, map);
        }
        Expression::MathExpr(_, args) => {
            for arg in args {
                replace_vars_by_const_in_expr(arg, map);
            }
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
            Line::ForwardDeclaration { var } => {
                assert!(!map.contains_key(var), "Variable {var} is a constant");
            }
            Line::Assignment { var, value } => {
                assert!(!map.contains_key(var), "Variable {var} is a constant");
                replace_vars_by_const_in_expr(value, map);
            }
            Line::ArrayAssign { array, index, value } => {
                if let SimpleExpr::Var(array_var) = array {
                    assert!(!map.contains_key(array_var), "Array {array_var} is a constant");
                }
                replace_vars_by_const_in_expr(index, map);
                replace_vars_by_const_in_expr(value, map);
            }
            Line::FunctionCall { args, return_data, .. } => {
                for arg in args {
                    replace_vars_by_const_in_expr(arg, map);
                }
                for target in return_data {
                    match target {
                        AssignmentTarget::Var(ret) => {
                            assert!(!map.contains_key(ret), "Return variable {ret} is a constant");
                        }
                        AssignmentTarget::ArrayAccess { array, index } => {
                            if let SimpleExpr::Var(array_var) = array {
                                assert!(!map.contains_key(array_var), "Array {array_var} is a constant");
                            }
                            replace_vars_by_const_in_expr(index, map);
                        }
                    }
                }
            }
            Line::IfCondition {
                condition,
                then_branch,
                else_branch,
                line_number: _,
            } => {
                match condition {
                    Condition::Comparison(cond) => {
                        replace_vars_by_const_in_expr(&mut cond.left, map);
                        replace_vars_by_const_in_expr(&mut cond.right, map);
                    }
                    Condition::Expression(expr, _assume_boolean) => {
                        replace_vars_by_const_in_expr(expr, map);
                    }
                }
                replace_vars_by_const_in_lines(then_branch, map);
                replace_vars_by_const_in_lines(else_branch, map);
            }
            Line::ForLoop { body, start, end, .. } => {
                replace_vars_by_const_in_expr(start, map);
                replace_vars_by_const_in_expr(end, map);
                replace_vars_by_const_in_lines(body, map);
            }
            Line::Assert { boolean, .. } => {
                replace_vars_by_const_in_expr(&mut boolean.left, map);
                replace_vars_by_const_in_expr(&mut boolean.right, map);
            }
            Line::FunctionRet { return_data } => {
                for ret in return_data {
                    replace_vars_by_const_in_expr(ret, map);
                }
            }
            Line::Precompile { table: _, args } => {
                for arg in args {
                    replace_vars_by_const_in_expr(arg, map);
                }
            }
            Line::Print { content, .. } => {
                for var in content {
                    replace_vars_by_const_in_expr(var, map);
                }
            }
            Line::CustomHint(_, decomposed_args) => {
                for expr in decomposed_args {
                    replace_vars_by_const_in_expr(expr, map);
                }
            }
            Line::PrivateInputStart { result } => {
                assert!(!map.contains_key(result), "Variable {result} is a constant");
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
            Self::ConstMallocAccess { malloc_label, offset } => {
                write!(f, "ConstMallocAccess({malloc_label}, {offset})")
            }
        }
    }
}

impl SimpleLine {
    fn to_string_with_indent(&self, indent: usize) -> String {
        let spaces = "    ".repeat(indent);
        let line_str = match self {
            Self::ForwardDeclaration { var } => {
                format!("var {var}")
            }
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
            Self::CustomHint(hint, args) => {
                format!(
                    "{}({})",
                    hint.name(),
                    args.iter().map(|expr| format!("{expr}")).collect::<Vec<_>>().join(", ")
                )
            }
            Self::RawAccess { res, index, shift } => {
                format!("{res} = memory[{index} + {shift}]")
            }
            Self::TestZero { operation, arg0, arg1 } => {
                format!("0 = {arg0} {operation} {arg1}")
            }
            Self::IfNotZero {
                condition,
                then_branch,
                else_branch,
                line_number: _,
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
                    format!("if {condition} != 0 {{\n{then_str}\n{spaces}}} else {{\n{else_str}\n{spaces}}}")
                }
            }
            Self::FunctionCall {
                function_name,
                args,
                return_data,
                line_number: _,
            } => {
                let args_str = args.iter().map(|arg| format!("{arg}")).collect::<Vec<_>>().join(", ");
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
            Self::Precompile {
                table: precompile,
                args,
            } => {
                format!(
                    "{}({})",
                    &precompile.name(),
                    args.iter().map(|arg| format!("{arg}")).collect::<Vec<_>>().join(", ")
                )
            }
            Self::Print { line_info: _, content } => {
                let content_str = content.iter().map(|c| format!("{c}")).collect::<Vec<_>>().join(", ");
                format!("print({content_str})")
            }
            Self::HintMAlloc { var, size } => {
                format!("{var} = malloc({size})")
            }
            Self::ConstMalloc { var, size, label: _ } => {
                format!("{var} = malloc({size})")
            }
            Self::PrivateInputStart { result } => {
                format!("private_input_start({result})")
            }
            Self::Panic => "panic".to_string(),
            Self::LocationReport { .. } => Default::default(),
            Self::DebugAssert(bool, _) => {
                format!("debug_assert({bool})")
            }
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
            write!(f, "fn {}({}) -> {} {{}}", self.name, args_str, self.n_returned_vars)
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
