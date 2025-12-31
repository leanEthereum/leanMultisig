use crate::{
    Counter, F,
    lang::{
        AssignmentTarget, Condition, ConstExpression, ConstMallocLabel, Context, Expression, Function, Line,
        MathOperation, Program, Scope, SimpleExpr, Var,
    },
    parser::ConstArrayValue,
};
use core::panic;
use lean_vm::{
    Boolean, BooleanExpr, CustomHint, FileId, FunctionName, SourceLineNumber, SourceLocation, Table, TableT,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::{Display, Formatter},
};
use utils::ToUsize;

#[derive(Debug, Clone)]
pub struct SimpleProgram {
    pub functions: BTreeMap<FunctionName, SimpleFunction>,
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
        Self::Memory(var_or_const)
    }
}

impl TryInto<VarOrConstMallocAccess> for SimpleExpr {
    type Error = ();

    fn try_into(self) -> Result<VarOrConstMallocAccess, Self::Error> {
        match self {
            Self::Memory(var_or_const) => Ok(var_or_const),
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
        operation: MathOperation, // add / sub / div / mul
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
    AssertZero {
        operation: MathOperation,
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

impl SimpleLine {
    pub fn equality(arg0: impl Into<VarOrConstMallocAccess>, arg1: impl Into<SimpleExpr>) -> Self {
        SimpleLine::Assignment {
            var: arg0.into(),
            operation: MathOperation::Add,
            arg0: arg1.into(),
            arg1: SimpleExpr::zero(),
        }
    }
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
    let ctx = SimplifyContext {
        functions: &program.functions,
        const_arrays: &program.const_arrays,
    };
    for (name, func) in &program.functions {
        let mut array_manager = ArrayManager::default();
        let mut mut_tracker = MutableVarTracker::default();

        for arg in &func.arguments {
            if arg.is_mutable {
                mut_tracker.register_mutable(&arg.name);
            }
        }

        let mut state = SimplifyState {
            counters: &mut counters,
            array_manager: &mut array_manager,
            mut_tracker: &mut mut_tracker,
            in_non_unrolled_loop: false,
        };
        let simplified_instructions = simplify_lines(
            &ctx,
            &mut state,
            &mut const_malloc,
            &mut new_functions,
            func.file_id,
            func.n_returned_vars,
            &func.body,
            false,
        );
        let arguments = func
            .arguments
            .iter()
            .map(|arg| {
                assert!(!arg.is_const);
                arg.name.clone()
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
        for arg in function.arguments.iter() {
            scope.vars.insert(arg.name.clone());
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
            Line::ForwardDeclaration { var, .. } => {
                ctx.add_var(var);
            }
            Line::Match { value, arms } => {
                check_expr_scoping(value, ctx);
                for (_, arm) in arms {
                    ctx.scopes.push(Scope { vars: BTreeSet::new() });
                    check_block_scoping(arm, ctx);
                    ctx.scopes.pop();
                }
            }
            Line::Statement { targets, value, .. } => {
                check_expr_scoping(value, ctx);
                // First: add new variables to scope
                for target in targets {
                    if let AssignmentTarget::Var { var, .. } = target
                        && !ctx.defines(var)
                    {
                        ctx.add_var(var);
                    }
                }
                // Second pass: check array access targets
                for target in targets {
                    if let AssignmentTarget::ArrayAccess { array: _, index } = target {
                        check_expr_scoping(index, ctx);
                    }
                }
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
                if !ctx.defines(var) {
                    ctx.add_var(var);
                }
            }
            Line::CustomHint(_, args) => {
                for arg in args {
                    check_expr_scoping(arg, ctx);
                }
            }
            Line::PrivateInputStart { result } => {
                ctx.add_var(result);
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
        Expression::ArrayAccess { array: _, index } => {
            for idx in index {
                check_expr_scoping(idx, ctx);
            }
        }
        Expression::MathExpr(_, args) => {
            for arg in args {
                check_expr_scoping(arg, ctx);
            }
        }
        Expression::FunctionCall { args, .. } => {
            for arg in args {
                check_expr_scoping(arg, ctx);
            }
        }
        Expression::Len { indices, .. } => {
            for idx in indices {
                check_expr_scoping(idx, ctx);
            }
        }
    }
}

/// Analyzes the simple expression to verify that each variable is defined in the given context.
fn check_simple_expr_scoping(expr: &SimpleExpr, ctx: &Context) {
    match expr {
        SimpleExpr::Memory(VarOrConstMallocAccess::Var(v)) => {
            assert!(ctx.defines(v), "Variable used but not defined: {v}");
        }
        SimpleExpr::Memory(VarOrConstMallocAccess::ConstMallocAccess { .. }) => {}
        SimpleExpr::Constant(_) => {}
    }
}

fn check_boolean_scoping(boolean: &BooleanExpr<Expression>, ctx: &Context) {
    check_expr_scoping(&boolean.left, ctx);
    check_expr_scoping(&boolean.right, ctx);
}

fn check_condition_scoping(condition: &Condition, ctx: &Context) {
    match condition {
        Condition::AssumeBoolean(expr) => {
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

impl Counters {
    fn aux_var(&mut self) -> Var {
        let var = format!("@aux_var_{}", self.aux_vars);
        self.aux_vars += 1;
        var
    }
}

struct SimplifyContext<'a> {
    functions: &'a BTreeMap<String, Function>,
    const_arrays: &'a BTreeMap<String, ConstArrayValue>,
}

struct SimplifyState<'a> {
    counters: &'a mut Counters,
    array_manager: &'a mut ArrayManager,
    mut_tracker: &'a mut MutableVarTracker,
    in_non_unrolled_loop: bool,
}

#[derive(Debug, Clone, Default)]
struct ArrayManager {
    counter: usize,
    aux_vars: BTreeMap<(Var, Expression), Var>, // (array, index) -> aux_var
    valid: BTreeSet<Var>,                       // currently valid aux vars
}

/// Tracks the current "version" of each mutable variable for SSA-like transformation
#[derive(Debug, Clone, Default)]
struct MutableVarTracker {
    /// Set of variables declared as mutable
    mutable_vars: BTreeSet<Var>,
    /// Maps original variable name -> current version number (0 = original)
    versions: BTreeMap<Var, usize>,
}

impl MutableVarTracker {
    /// Check if a variable is mutable
    fn is_mutable(&self, var: &Var) -> bool {
        self.mutable_vars.contains(var)
    }

    /// Register a new mutable variable
    fn register_mutable(&mut self, var: &Var) {
        self.mutable_vars.insert(var.clone());
        self.versions.insert(var.clone(), 0);
    }

    /// Get the current variable name (with version suffix if mutated)
    fn current_name(&self, var: &Var) -> Var {
        match self.versions.get(var) {
            Some(0) | None => var.clone(),
            Some(v) => format!("@mut_{var}_{v}"),
        }
    }

    /// Get the current version number for a variable
    fn current_version(&self, var: &Var) -> usize {
        self.versions.get(var).copied().unwrap_or(0)
    }

    /// Increment version and return new variable name
    fn increment_version(&mut self, var: &Var) -> Var {
        let version = self.versions.entry(var.clone()).or_insert(0);
        *version += 1;
        format!("@mut_{var}_{version}")
    }

    /// Snapshot current versions (for if/else handling)
    fn snapshot_versions(&self) -> BTreeMap<Var, usize> {
        self.versions.clone()
    }

    /// Restore versions from snapshot
    fn restore_versions(&mut self, snapshot: BTreeMap<Var, usize>) {
        self.versions = snapshot;
    }
}

#[derive(Debug, Clone, Default)]
pub struct ConstMalloc {
    counter: usize,
    map: BTreeMap<Var, ConstMallocLabel>,
}

impl ArrayManager {
    fn get_aux_var(&mut self, array: &Var, index: &Expression) -> Var {
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
    ctx: &SimplifyContext<'_>,
    state: &mut SimplifyState<'_>,
    const_malloc: &mut ConstMalloc,
    new_functions: &mut BTreeMap<String, SimpleFunction>,
    file_id: FileId,
    n_returned_vars: usize,
    lines: &[Line],
    in_a_loop: bool,
) -> Vec<SimpleLine> {
    let mut res = Vec::new();
    for line in lines {
        match line {
            Line::ForwardDeclaration { var, mutable } => {
                if *mutable {
                    state.mut_tracker.register_mutable(var);
                }
                res.push(SimpleLine::ForwardDeclaration { var: var.clone() });
            }
            Line::Match { value, arms } => {
                let simple_value = simplify_expr(ctx, state, const_malloc, value, &mut res);
                let mut simple_arms = vec![];
                for (i, (pattern, statements)) in arms.iter().enumerate() {
                    assert_eq!(*pattern, i, "match patterns should be consecutive, starting from 0");
                    simple_arms.push(simplify_lines(
                        ctx,
                        state,
                        const_malloc,
                        new_functions,
                        file_id,
                        n_returned_vars,
                        statements,
                        in_a_loop,
                    ));
                }
                res.push(SimpleLine::Match {
                    value: simple_value,
                    arms: simple_arms,
                });
            }
            Line::Statement {
                targets,
                value,
                line_number,
            } => {
                // Helper function to get the target variable name, handling mutable variable versioning
                let get_target_var_name = |state: &mut SimplifyState<'_>, var: &Var, is_mutable: bool, line_number: usize| -> Var {
                    if is_mutable {
                        // First assignment with `mut` - register as mutable
                        state.mut_tracker.register_mutable(var);
                        var.clone()
                    } else if state.mut_tracker.is_mutable(var) {
                        // Re-assignment to a mutable variable
                        if state.in_non_unrolled_loop {
                            panic!(
                                "Cannot mutate variable '{}' inside a non-unrolled loop at line {}",
                                var, line_number
                            );
                        }
                        // Increment version and get new variable name
                        state.mut_tracker.increment_version(var)
                    } else {
                        // Regular assignment to non-mutable variable
                        var.clone()
                    }
                };

                match value {
                    Expression::FunctionCall { function_name, args } => {
                        // Function call - may have zero, one, or multiple targets
                        let function = ctx.functions.get(function_name).unwrap_or_else(|| {
                            panic!("Function used but not defined: {function_name}, at line {line_number}")
                        });
                        if targets.len() != function.n_returned_vars {
                            panic!(
                                "Expected {} returned vars (and not {}) in call to {function_name}, at line {line_number}",
                                function.n_returned_vars,
                                targets.len()
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
                            .map(|arg| simplify_expr(ctx, state, const_malloc, arg, &mut res))
                            .collect::<Vec<_>>();

                        let mut temp_vars = Vec::new();
                        let mut array_targets: Vec<(usize, Var, Box<Expression>)> = Vec::new();

                        for (i, target) in targets.iter().enumerate() {
                            match target {
                                AssignmentTarget::Var { var, is_mutable } => {
                                    let target_var = get_target_var_name(state, var, *is_mutable, *line_number);
                                    // Add forward declaration for new versioned variable
                                    if *is_mutable || state.mut_tracker.current_version(var) > 0 {
                                        res.push(SimpleLine::ForwardDeclaration { var: target_var.clone() });
                                    }
                                    temp_vars.push(target_var);
                                }
                                AssignmentTarget::ArrayAccess { array, index } => {
                                    temp_vars.push(state.counters.aux_var());
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
                            let simplified_index =
                                simplify_expr(ctx, state, const_malloc, &index, &mut res);
                            let simplified_value =
                                VarOrConstMallocAccess::Var(temp_vars[i].clone()).into();
                            handle_array_assignment(
                                ctx,
                                state,
                                &mut res,
                                &array,
                                &[simplified_index],
                                ArrayAccessType::ArrayIsAssigned(simplified_value),
                            );
                        }
                    }
                    _ => {
                        assert!(targets.len() == 1, "Non-function call must have exactly one target");
                        let target = &targets[0];

                        match target {
                            AssignmentTarget::Var { var, is_mutable } => {
                                // IMPORTANT: Simplify RHS BEFORE updating version tracker
                                // This ensures the RHS uses the current (old) version of any mutable variables
                                match value {
                                    Expression::Value(val) => {
                                        let simplified_val = simplify_expr(
                                            ctx,
                                            state,
                                            const_malloc,
                                            &Expression::Value(val.clone()),
                                            &mut res,
                                        );
                                        let target_var =
                                            get_target_var_name(state, var, *is_mutable, *line_number);
                                        if state.mut_tracker.is_mutable(var)
                                            && state.mut_tracker.current_version(var) > 0
                                        {
                                            res.push(SimpleLine::ForwardDeclaration {
                                                var: target_var.clone(),
                                            });
                                        }
                                        res.push(SimpleLine::equality(target_var, simplified_val));
                                    }
                                    Expression::ArrayAccess { array, index } => {
                                        // Pre-simplify indices before version update
                                        let simplified_index: Vec<SimpleExpr> = index
                                            .iter()
                                            .map(|idx| simplify_expr(ctx, state, const_malloc, idx, &mut res))
                                            .collect();
                                        let target_var =
                                            get_target_var_name(state, var, *is_mutable, *line_number);
                                        if state.mut_tracker.is_mutable(var)
                                            && state.mut_tracker.current_version(var) > 0
                                        {
                                            res.push(SimpleLine::ForwardDeclaration {
                                                var: target_var.clone(),
                                            });
                                        }
                                        handle_array_assignment(
                                            ctx,
                                            state,
                                            &mut res,
                                            array,
                                            &simplified_index,
                                            ArrayAccessType::VarIsAssigned(target_var),
                                        );
                                    }
                                    Expression::MathExpr(operation, args) => {
                                        let args_simplified: Vec<SimpleExpr> = args
                                            .iter()
                                            .map(|arg| simplify_expr(ctx, state, const_malloc, arg, &mut res))
                                            .collect();
                                        let target_var =
                                            get_target_var_name(state, var, *is_mutable, *line_number);
                                        if state.mut_tracker.is_mutable(var)
                                            && state.mut_tracker.current_version(var) > 0
                                        {
                                            res.push(SimpleLine::ForwardDeclaration {
                                                var: target_var.clone(),
                                            });
                                        }
                                        // If all operands are constants, evaluate at compile time
                                        if let Some(const_args) =
                                            SimpleExpr::try_vec_as_constant(&args_simplified)
                                        {
                                            let result = ConstExpression::MathExpr(*operation, const_args);
                                            res.push(SimpleLine::equality(
                                                target_var,
                                                SimpleExpr::Constant(result),
                                            ));
                                        } else {
                                            res.push(SimpleLine::Assignment {
                                                var: target_var.into(),
                                                operation: *operation,
                                                arg0: args_simplified[0].clone(),
                                                arg1: args_simplified[1].clone(),
                                            });
                                        }
                                    }
                                    Expression::Len { .. } => unreachable!(),
                                    Expression::FunctionCall { .. } => {
                                        unreachable!("FunctionCall should be handled above")
                                    }
                                }
                            }
                            AssignmentTarget::ArrayAccess { array, index } => {
                                // Array element assignment - pre-simplify both index and value
                                let simplified_index =
                                    vec![simplify_expr(ctx, state, const_malloc, index, &mut res)];
                                let simplified_value =
                                    simplify_expr(ctx, state, const_malloc, value, &mut res);
                                handle_array_assignment(
                                    ctx,
                                    state,
                                    &mut res,
                                    array,
                                    &simplified_index,
                                    ArrayAccessType::ArrayIsAssigned(simplified_value),
                                );
                            }
                        }
                    }
                }
            }
            Line::Assert {
                boolean,
                line_number,
                debug,
            } => {
                let left = simplify_expr(ctx, state, const_malloc, &boolean.left, &mut res);
                let right = simplify_expr(ctx, state, const_malloc, &boolean.right, &mut res);

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
                            let diff_var = state.counters.aux_var();
                            res.push(SimpleLine::Assignment {
                                var: diff_var.clone().into(),
                                operation: MathOperation::Sub,
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
                            let (var, other): (VarOrConstMallocAccess, _) = if let Ok(left) = left.clone().try_into() {
                                (left, right)
                            } else if let Ok(right) = right.clone().try_into() {
                                (right, left)
                            } else {
                                // Both are constants - evaluate at compile time
                                if let (SimpleExpr::Constant(left_const), SimpleExpr::Constant(right_const)) =
                                    (&left, &right)
                                    && let (Some(left_val), Some(right_val)) =
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
                                panic!("Unsupported equality assertion: {left:?}, {right:?}")
                            };
                            res.push(SimpleLine::equality(var, other));
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

                        let left_simplified = simplify_expr(ctx, state, const_malloc, left, &mut res);
                        let right_simplified = simplify_expr(ctx, state, const_malloc, right, &mut res);

                        let diff_var = state.counters.aux_var();
                        res.push(SimpleLine::Assignment {
                            var: diff_var.clone().into(),
                            operation: MathOperation::Sub,
                            arg0: left_simplified,
                            arg1: right_simplified,
                        });
                        (diff_var.into(), then_branch, else_branch)
                    }
                    Condition::AssumeBoolean(condition) => {
                        let condition_simplified = simplify_expr(ctx, state, const_malloc, condition, &mut res);
                        (condition_simplified, then_branch, else_branch)
                    }
                };

                // Snapshot mutable variable versions before processing branches
                let mut_tracker_snapshot = state.mut_tracker.snapshot_versions();

                let mut array_manager_then = state.array_manager.clone();
                let mut mut_tracker_then = state.mut_tracker.clone();
                let mut state_then = SimplifyState {
                    counters: state.counters,
                    array_manager: &mut array_manager_then,
                    mut_tracker: &mut mut_tracker_then,
                    in_non_unrolled_loop: state.in_non_unrolled_loop,
                };
                let mut then_branch_simplified = simplify_lines(
                    ctx,
                    &mut state_then,
                    const_malloc,
                    new_functions,
                    file_id,
                    n_returned_vars,
                    then_branch,
                    in_a_loop,
                );
                let then_versions = mut_tracker_then.versions.clone();

                let mut array_manager_else = array_manager_then.clone();
                array_manager_else.valid = state.array_manager.valid.clone(); // Crucial: remove the access added in the IF branch

                // Restore mutable variable versions for else branch
                let mut mut_tracker_else = state.mut_tracker.clone();
                mut_tracker_else.restore_versions(mut_tracker_snapshot);

                let mut state_else = SimplifyState {
                    counters: state.counters,
                    array_manager: &mut array_manager_else,
                    mut_tracker: &mut mut_tracker_else,
                    in_non_unrolled_loop: state.in_non_unrolled_loop,
                };
                let mut else_branch_simplified = simplify_lines(
                    ctx,
                    &mut state_else,
                    const_malloc,
                    new_functions,
                    file_id,
                    n_returned_vars,
                    else_branch,
                    in_a_loop,
                );
                let else_versions = mut_tracker_else.versions.clone();

                // Merge mutable variable versions: ensure both branches end with same version
                // First, collect all variables that need unification and their unified var names
                let mut unifications = Vec::new();
                let snapshot_versions = state.mut_tracker.snapshot_versions();
                for var in state.mut_tracker.mutable_vars.iter() {
                    let snapshot_v = snapshot_versions.get(var).copied().unwrap_or(0);
                    let then_v = then_versions.get(var).copied().unwrap_or(0);
                    let else_v = else_versions.get(var).copied().unwrap_or(0);

                    if then_v != else_v {
                        // Need to unify - create a new version for post-if/else
                        let unified_version = then_v.max(else_v) + 1;
                        let unified_var = format!("@mut_{var}_{unified_version}");

                        // Get variable names for each branch
                        let then_var_name = if then_v == 0 { var.clone() } else { format!("@mut_{var}_{then_v}") };
                        let else_var_name = if else_v == 0 { var.clone() } else { format!("@mut_{var}_{else_v}") };

                        unifications.push((var.clone(), unified_var, unified_version, then_var_name, else_var_name));
                    } else {
                        // Both branches have same version
                        if then_v > snapshot_v {
                            // A new versioned variable was created in both branches
                            // We need to add a forward declaration before the if/else
                            // so the variable is in scope after the if/else
                            let versioned_var = format!("@mut_{var}_{then_v}");
                            res.push(SimpleLine::ForwardDeclaration { var: versioned_var });
                        }
                        state.mut_tracker.versions.insert(var.clone(), then_v);
                    }
                }

                // Add forward declarations BEFORE the if/else for all unified variables
                for (_, unified_var, _, _, _) in &unifications {
                    res.push(SimpleLine::ForwardDeclaration { var: unified_var.clone() });
                }

                // Add equality assignments at the end of each branch
                for (var, unified_var, unified_version, then_var_name, else_var_name) in unifications {
                    then_branch_simplified.push(SimpleLine::equality(
                        unified_var.clone(),
                        SimpleExpr::Memory(VarOrConstMallocAccess::Var(then_var_name)),
                    ));

                    else_branch_simplified.push(SimpleLine::equality(
                        unified_var.clone(),
                        SimpleExpr::Memory(VarOrConstMallocAccess::Var(else_var_name)),
                    ));

                    state.mut_tracker.versions.insert(var, unified_version);
                }

                *state.array_manager = array_manager_else.clone();
                // keep the intersection both branches
                state.array_manager.valid = state
                    .array_manager
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
                let valid_aux_vars_in_array_manager_before = state.array_manager.valid.clone();
                state.array_manager.valid.clear();

                // Set flag to detect mutation inside non-unrolled loop
                let was_in_non_unrolled_loop = state.in_non_unrolled_loop;
                state.in_non_unrolled_loop = true;

                let simplified_body = simplify_lines(
                    ctx,
                    state,
                    &mut loop_const_malloc,
                    new_functions,
                    file_id,
                    0,
                    body,
                    true,
                );

                state.in_non_unrolled_loop = was_in_non_unrolled_loop;
                const_malloc.counter = loop_const_malloc.counter;
                state.array_manager.valid = valid_aux_vars_in_array_manager_before; // restore the valid aux vars

                let func_name = format!("@loop_{}_line_{}", state.counters.loops, line_number);
                state.counters.loops += 1;

                // Find variables used inside loop but defined outside
                let (_, mut external_vars) = find_variable_usage(body, ctx.const_arrays);

                // Include variables in start/end
                for expr in [start, end] {
                    for var in vars_in_expression(expr, ctx.const_arrays) {
                        external_vars.insert(var);
                    }
                }
                external_vars.remove(iterator); // Iterator is internal to loop

                let mut external_vars: Vec<_> = external_vars.into_iter().collect();

                let start_simplified = simplify_expr(ctx, state, const_malloc, start, &mut res);
                let mut end_simplified = simplify_expr(ctx, state, const_malloc, end, &mut res);
                if let SimpleExpr::Memory(VarOrConstMallocAccess::ConstMallocAccess { malloc_label, offset }) =
                    end_simplified.clone()
                {
                    // we use an auxilary variable to store the end value (const malloc inside non-unrolled loops does not work)
                    let aux_end_var = state.counters.aux_var();
                    res.push(SimpleLine::equality(
                        aux_end_var.clone(),
                        VarOrConstMallocAccess::ConstMallocAccess { malloc_label, offset },
                    ));
                    end_simplified = VarOrConstMallocAccess::Var(aux_end_var).into();
                }

                for (simplified, original) in [
                    (start_simplified.clone(), start.clone()),
                    (end_simplified.clone(), end.clone()),
                ] {
                    if !matches!(original, Expression::Value(_)) {
                        // the simplified var is auxiliary
                        if let SimpleExpr::Memory(VarOrConstMallocAccess::Var(var)) = simplified {
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
            Line::FunctionRet { return_data } => {
                assert!(!in_a_loop, "Function return inside a loop is not currently supported");
                assert!(
                    return_data.len() == n_returned_vars,
                    "Wrong number of return values in return statement; expected {n_returned_vars} but got {}",
                    return_data.len()
                );
                let simplified_return_data = return_data
                    .iter()
                    .map(|ret| simplify_expr(ctx, state, const_malloc, ret, &mut res))
                    .collect::<Vec<_>>();
                res.push(SimpleLine::FunctionRet {
                    return_data: simplified_return_data,
                });
            }
            Line::Precompile { table, args } => {
                let simplified_args = args
                    .iter()
                    .map(|arg| simplify_expr(ctx, state, const_malloc, arg, &mut res))
                    .collect::<Vec<_>>();
                res.push(SimpleLine::Precompile {
                    table: *table,
                    args: simplified_args,
                });
            }
            Line::Print { line_info, content } => {
                let simplified_content = content
                    .iter()
                    .map(|var| simplify_expr(ctx, state, const_malloc, var, &mut res))
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
                let simplified_size = simplify_expr(ctx, state, const_malloc, size, &mut res);
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
                    .map(|expr| simplify_expr(ctx, state, const_malloc, expr, &mut res))
                    .collect::<Vec<_>>();
                res.push(SimpleLine::CustomHint(*hint, simplified_args));
            }
            Line::Panic => {
                res.push(SimpleLine::Panic);
            }
            Line::LocationReport { location } => {
                res.push(SimpleLine::LocationReport { location: *location });
            }
        }
    }

    res
}

fn simplify_expr(
    ctx: &SimplifyContext<'_>,
    state: &mut SimplifyState<'_>,
    const_malloc: &ConstMalloc,
    expr: &Expression,
    lines: &mut Vec<SimpleLine>,
) -> SimpleExpr {
    match expr {
        Expression::Value(value) => {
            // Translate mutable variable references to their current versioned name
            if let SimpleExpr::Memory(VarOrConstMallocAccess::Var(var)) = value {
                let versioned_var = state.mut_tracker.current_name(var);
                SimpleExpr::Memory(VarOrConstMallocAccess::Var(versioned_var))
            } else {
                value.clone()
            }
        }
        Expression::ArrayAccess { array, index } => {
            // Check for const array access
            if let Some(arr) = ctx.const_arrays.get(array) {
                let simplified_index = index
                    .iter()
                    .map(|idx| {
                        simplify_expr(ctx, state, const_malloc, idx, lines)
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

            if let Some(label) = const_malloc.map.get(array)
                && let Ok(offset) = ConstExpression::try_from(index.clone())
            {
                return VarOrConstMallocAccess::ConstMallocAccess {
                    malloc_label: *label,
                    offset,
                }
                .into();
            }

            let aux_arr = state.array_manager.get_aux_var(array, &index); // auxiliary var to store m[array + index]

            if !state.array_manager.valid.insert(aux_arr.clone()) {
                return VarOrConstMallocAccess::Var(aux_arr).into();
            }

            let simplified_index = simplify_expr(ctx, state, const_malloc, &index, lines);
            handle_array_assignment(
                ctx,
                state,
                lines,
                array,
                &[simplified_index],
                ArrayAccessType::VarIsAssigned(aux_arr.clone()),
            );
            VarOrConstMallocAccess::Var(aux_arr).into()
        }
        Expression::MathExpr(operation, args) => {
            let simplified_args = args
                .iter()
                .map(|arg| simplify_expr(ctx, state, const_malloc, arg, lines))
                .collect::<Vec<_>>();
            if let Some(const_args) = SimpleExpr::try_vec_as_constant(&simplified_args) {
                return SimpleExpr::Constant(ConstExpression::MathExpr(*operation, const_args));
            }
            let aux_var = state.counters.aux_var();
            assert_eq!(simplified_args.len(), 2);
            lines.push(SimpleLine::Assignment {
                var: aux_var.clone().into(),
                operation: *operation,
                arg0: simplified_args[0].clone(),
                arg1: simplified_args[1].clone(),
            });
            VarOrConstMallocAccess::Var(aux_var).into()
        }
        Expression::FunctionCall { function_name, args } => {
            let function = ctx
                .functions
                .get(function_name)
                .unwrap_or_else(|| panic!("Function used but not defined: {function_name}"));
            assert_eq!(
                function.n_returned_vars, 1,
                "Nested function call to '{function_name}' must return exactly 1 value, but returns {}",
                function.n_returned_vars
            );

            let simplified_args = args
                .iter()
                .map(|arg| simplify_expr(ctx, state, const_malloc, arg, lines))
                .collect::<Vec<_>>();

            // Create a temporary variable for the function result
            let result_var = state.counters.aux_var();

            lines.push(SimpleLine::FunctionCall {
                function_name: function_name.clone(),
                args: simplified_args,
                return_data: vec![result_var.clone()],
                line_number: 0, // No source line number for nested calls
            });

            VarOrConstMallocAccess::Var(result_var).into()
        }
        Expression::Len { .. } => unreachable!(),
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
            Condition::AssumeBoolean(expr) => {
                on_new_expr(expr, internal_vars, external_vars);
            }
        };

    for line in lines {
        match line {
            Line::ForwardDeclaration { var, .. } => {
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
            Line::Statement { targets, value, .. } => {
                on_new_expr(value, &internal_vars, &mut external_vars);
                for target in targets {
                    match target {
                        AssignmentTarget::Var { var, .. } => {
                            // Only mark as internal if not already used as external
                            // This ensures re-assignments to external (mutable) variables
                            // keep them as external
                            if !external_vars.contains(var) {
                                internal_vars.insert(var.clone());
                            }
                        }
                        AssignmentTarget::ArrayAccess { array, index } => {
                            assert!(!const_arrays.contains_key(array), "Cannot assign to const array");
                            if !internal_vars.contains(array) {
                                external_vars.insert(array.clone());
                            }
                            on_new_expr(index, &internal_vars, &mut external_vars);
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
            Line::Panic | Line::Break | Line::LocationReport { .. } => {}
        }
    }

    (internal_vars, external_vars)
}

fn inline_simple_expr(simple_expr: &mut SimpleExpr, args: &BTreeMap<Var, SimpleExpr>, inlining_count: usize) {
    if let SimpleExpr::Memory(VarOrConstMallocAccess::Var(var)) = simple_expr {
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
            if let Some(replacement) = args.get(array) {
                let SimpleExpr::Memory(VarOrConstMallocAccess::Var(new_array)) = replacement else {
                    panic!("Cannot inline array access with non-variable array argument");
                };
                *array = new_array.clone();
            } else {
                *array = format!("@inlined_var_{inlining_count}_{array}");
            }
            for idx in index {
                inline_expr(idx, args, inlining_count);
            }
        }
        Expression::MathExpr(_, math_args) => {
            for arg in math_args {
                inline_expr(arg, args, inlining_count);
            }
        }
        Expression::FunctionCall { args: func_args, .. } => {
            for arg in func_args {
                inline_expr(arg, args, inlining_count);
            }
        }
        Expression::Len { indices, .. } => {
            for idx in indices {
                inline_expr(idx, args, inlining_count);
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
        Condition::AssumeBoolean(expr) => inline_expr(expr, args, inlining_count),
    };

    let inline_internal_var = |var: &mut Var| {
        if let Some(replacement) = args.get(var) {
            // Variable is a mutable argument - replace with the caller's variable
            let SimpleExpr::Memory(VarOrConstMallocAccess::Var(new_var)) = replacement else {
                panic!("Cannot inline mutable argument re-assignment with non-variable argument");
            };
            *var = new_var.clone();
        } else {
            // Internal variable - rename with inlining prefix
            *var = format!("@inlined_var_{inlining_count}_{var}");
        }
    };

    let mut lines_to_replace = vec![];
    for (i, line) in lines.iter_mut().enumerate() {
        match line {
            Line::ForwardDeclaration { var, .. } => {
                inline_internal_var(var);
            }
            Line::Match { value, arms } => {
                inline_expr(value, args, inlining_count);
                for (_, statements) in arms {
                    inline_lines(statements, args, res, inlining_count);
                }
            }
            Line::Statement { targets, value, .. } => {
                inline_expr(value, args, inlining_count);
                for target in targets {
                    match target {
                        AssignmentTarget::Var { var, .. } => {
                            inline_internal_var(var);
                        }
                        AssignmentTarget::ArrayAccess { array, index } => {
                            if let Some(replacement) = args.get(array) {
                                // Array is a function argument - replace with the argument's var name
                                let SimpleExpr::Memory(VarOrConstMallocAccess::Var(new_array)) = replacement else {
                                    panic!("Cannot inline array access target with non-variable array argument");
                                };
                                *array = new_array.clone();
                            } else {
                                // Internal variable - rename with inlining prefix
                                *array = format!("@inlined_var_{inlining_count}_{array}");
                            }
                            inline_expr(index, args, inlining_count);
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
                inline_condition(condition);

                inline_lines(then_branch, args, res, inlining_count);
                inline_lines(else_branch, args, res, inlining_count);
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
                        .map(|(target, expr)| Line::Statement {
                            targets: vec![target.clone()],
                            value: expr.clone(),
                            line_number: 0,
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
            if let SimpleExpr::Memory(VarOrConstMallocAccess::Var(var)) = value {
                vars.insert(var.clone());
            }
        }
        Expression::ArrayAccess { array, index } => {
            if !const_arrays.contains_key(array) {
                vars.insert(array.clone());
            }
            for idx in index {
                vars.extend(vars_in_expression(idx, const_arrays));
            }
        }
        Expression::MathExpr(_, args) => {
            for arg in args {
                vars.extend(vars_in_expression(arg, const_arrays));
            }
        }
        Expression::FunctionCall { args, .. } => {
            for arg in args {
                vars.extend(vars_in_expression(arg, const_arrays));
            }
        }
        Expression::Len { indices, .. } => {
            for idx in indices {
                vars.extend(vars_in_expression(idx, const_arrays));
            }
        }
    }
    vars
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ArrayAccessType {
    VarIsAssigned(Var),         // var = array[index]
    ArrayIsAssigned(SimpleExpr), // array[index] = expr
}

fn handle_array_assignment(
    ctx: &SimplifyContext<'_>,
    state: &mut SimplifyState<'_>,
    res: &mut Vec<SimpleLine>,
    array: &Var,
    simplified_index: &[SimpleExpr],
    access_type: ArrayAccessType,
) {
    if let ArrayAccessType::VarIsAssigned(var) = &access_type
        && let Some(const_array) = ctx.const_arrays.get(array)
    {
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
        res.push(SimpleLine::equality(var.clone(), ConstExpression::from(value)));
        return;
    }

    let value_simplified = match access_type {
        ArrayAccessType::VarIsAssigned(var) => SimpleExpr::Memory(VarOrConstMallocAccess::Var(var)),
        ArrayAccessType::ArrayIsAssigned(expr) => expr,
    };

    // TODO opti: in some case we could use ConstMallocAccess
    assert_eq!(simplified_index.len(), 1);
    let simplified_index = simplified_index[0].clone();
    let (index_var, shift) = match simplified_index {
        SimpleExpr::Constant(c) => (SimpleExpr::Memory(VarOrConstMallocAccess::Var(array.clone())), c),
        _ => {
            // Create pointer variable: ptr = array + index
            let ptr_var = state.counters.aux_var();
            res.push(SimpleLine::Assignment {
                var: ptr_var.clone().into(),
                operation: MathOperation::Add,
                arg0: SimpleExpr::Memory(VarOrConstMallocAccess::Var(array.clone())),
                arg1: simplified_index,
            });
            (
                SimpleExpr::Memory(VarOrConstMallocAccess::Var(ptr_var)),
                ConstExpression::zero(),
            )
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
        operation: MathOperation::Add,
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
            operation: MathOperation::Sub,
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
            SimpleExpr::Memory(VarOrConstMallocAccess::Var(var)) => {
                if var == iterator {
                    *value_expr = SimpleExpr::Constant(ConstExpression::from(iterator_value));
                } else if internal_vars.contains(var) {
                    *var = format!("@unrolled_{unroll_index}_{iterator_value}_{var}");
                }
            }
            SimpleExpr::Constant(_) | SimpleExpr::Memory(VarOrConstMallocAccess::ConstMallocAccess { .. }) => {}
        },
        Expression::ArrayAccess { array, index } => {
            assert!(array != iterator, "Weird");
            if internal_vars.contains(array) {
                *array = format!("@unrolled_{unroll_index}_{iterator_value}_{array}");
            }
            for index in index {
                replace_vars_for_unroll_in_expr(index, iterator, unroll_index, iterator_value, internal_vars);
            }
        }
        Expression::MathExpr(_, args) => {
            for arg in args {
                replace_vars_for_unroll_in_expr(arg, iterator, unroll_index, iterator_value, internal_vars);
            }
        }
        Expression::FunctionCall { args, .. } => {
            for arg in args {
                replace_vars_for_unroll_in_expr(arg, iterator, unroll_index, iterator_value, internal_vars);
            }
        }
        Expression::Len { indices, .. } => {
            for idx in indices {
                replace_vars_for_unroll_in_expr(idx, iterator, unroll_index, iterator_value, internal_vars);
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
            Line::ForwardDeclaration { var, .. } => {
                *var = format!("@unrolled_{unroll_index}_{iterator_value}_{var}");
            }
            Line::Statement { targets, value, .. } => {
                replace_vars_for_unroll_in_expr(value, iterator, unroll_index, iterator_value, internal_vars);
                for target in targets {
                    match target {
                        AssignmentTarget::Var { var, .. } => {
                            assert!(var != iterator, "Weird");
                            // Only rename internal variables - external (mutable) vars keep their name
                            if internal_vars.contains(var) {
                                *var = format!("@unrolled_{unroll_index}_{iterator_value}_{var}");
                            }
                        }
                        AssignmentTarget::ArrayAccess { array, index } => {
                            assert!(array != iterator, "Weird");
                            if internal_vars.contains(array) {
                                *array = format!("@unrolled_{unroll_index}_{iterator_value}_{array}");
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
                    Condition::AssumeBoolean(expr) => {
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

    let mut counter1 = Counter::new();
    let mut counter2 = Counter::new();

    while max_iterations > 0 {
        let mut any_changes = false;

        // Process non-inlined functions
        for func in program.functions.values_mut() {
            if !func.inlined {
                let old_body = func.body.clone();

                let mut ctx = Context::new();
                for arg in func.arguments.iter() {
                    ctx.add_var(&arg.name);
                }
                func.body = handle_inlined_functions_helper(
                    &mut ctx,
                    &func.body,
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
                let old_body = func.body.clone();

                let mut ctx = Context::new();
                for arg in func.arguments.iter() {
                    ctx.add_var(&arg.name);
                }
                handle_inlined_functions_helper(&mut ctx, &func.body, &inlined_functions, &mut counter1, &mut counter2);

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

/// Recursively extracts inlined function calls from an expression.
/// Returns the modified expression and lines to prepend (forward declarations and function calls).
fn extract_inlined_calls_from_expr(
    expr: &Expression,
    inlined_functions: &BTreeMap<String, Function>,
    inlined_var_counter: &mut Counter,
) -> (Expression, Vec<Line>) {
    let mut lines = vec![];

    match expr {
        Expression::Value(_) => (expr.clone(), vec![]),
        Expression::ArrayAccess { array, index } => {
            let mut index_new = vec![];
            for idx in index {
                let (idx, idx_lines) = extract_inlined_calls_from_expr(idx, inlined_functions, inlined_var_counter);
                lines.extend(idx_lines);
                index_new.push(idx);
            }
            (
                Expression::ArrayAccess {
                    array: array.clone(),
                    index: index_new,
                },
                lines,
            )
        }
        Expression::MathExpr(operation, args) => {
            let mut args_new = vec![];
            for arg in args {
                let (arg, arg_lines) = extract_inlined_calls_from_expr(arg, inlined_functions, inlined_var_counter);
                lines.extend(arg_lines);
                args_new.push(arg);
            }
            (Expression::MathExpr(*operation, args_new), lines)
        }
        Expression::FunctionCall { function_name, args } => {
            let mut args_new = vec![];
            for arg in args {
                let (arg, arg_lines) = extract_inlined_calls_from_expr(arg, inlined_functions, inlined_var_counter);
                args_new.push(arg);
                lines.extend(arg_lines);
            }

            if inlined_functions.contains_key(function_name) {
                let aux_var = format!("@inlined_var_{}", inlined_var_counter.next());
                lines.push(Line::ForwardDeclaration { var: aux_var.clone(), mutable: false });
                lines.push(Line::Statement {
                    targets: vec![AssignmentTarget::Var {
                        var: aux_var.clone(),
                        is_mutable: false,
                    }],
                    value: Expression::FunctionCall {
                        function_name: function_name.clone(),
                        args: args.clone(),
                    },
                    line_number: 0,
                });
                (Expression::Value(VarOrConstMallocAccess::Var(aux_var).into()), lines)
            } else {
                (expr.clone(), lines)
            }
        }
        Expression::Len { array, indices } => {
            let mut new_indices = vec![];
            for idx in indices.iter() {
                let (idx, idx_lines) = extract_inlined_calls_from_expr(idx, inlined_functions, inlined_var_counter);
                lines.extend(idx_lines);
                new_indices.push(idx);
            }
            (
                Expression::Len {
                    array: array.clone(),
                    indices: new_indices,
                },
                lines,
            )
        }
    }
}

fn extract_inlined_calls_from_boolean_expr(
    boolean: &BooleanExpr<Expression>,
    inlined_functions: &BTreeMap<String, Function>,
    inlined_var_counter: &mut Counter,
) -> (BooleanExpr<Expression>, Vec<Line>) {
    let (left, mut lines) = extract_inlined_calls_from_expr(&boolean.left, inlined_functions, inlined_var_counter);
    let (right, right_lines) = extract_inlined_calls_from_expr(&boolean.right, inlined_functions, inlined_var_counter);
    lines.extend(right_lines);
    let boolean = BooleanExpr {
        kind: boolean.kind,
        left,
        right,
    };
    (boolean, lines)
}

fn extract_inlined_calls_from_condition(
    condition: &Condition,
    inlined_functions: &BTreeMap<String, Function>,
    inlined_var_counter: &mut Counter,
) -> (Condition, Vec<Line>) {
    match condition {
        Condition::AssumeBoolean(expr) => {
            let (expr, expr_lines) = extract_inlined_calls_from_expr(expr, inlined_functions, inlined_var_counter);
            (Condition::AssumeBoolean(expr), expr_lines)
        }
        Condition::Comparison(boolean) => {
            let (boolean, boolean_lines) =
                extract_inlined_calls_from_boolean_expr(boolean, inlined_functions, inlined_var_counter);
            (Condition::Comparison(boolean), boolean_lines)
        }
    }
}

fn handle_inlined_functions_helper(
    ctx: &mut Context,
    lines_in: &Vec<Line>,
    inlined_functions: &BTreeMap<String, Function>,
    inlined_var_counter: &mut Counter,
    total_inlined_counter: &mut Counter,
) -> Vec<Line> {
    let mut lines_out = vec![];
    for line in lines_in {
        match line {
            Line::Break | Line::Panic | Line::LocationReport { .. } => {
                lines_out.push(line.clone());
            }
            Line::Statement {
                targets,
                value: Expression::FunctionCall { function_name, args },
                line_number: _,
            } => {
                if let Some(func) = inlined_functions.get(function_name) {
                    let mut inlined_lines = vec![];

                    // Only add forward declarations for variable targets, not array accesses
                    for target in targets.iter() {
                        if let AssignmentTarget::Var { var, .. } = target
                            && !ctx.defines(var)
                        {
                            inlined_lines.push(Line::ForwardDeclaration { var: var.clone(), mutable: false });
                            ctx.add_var(var);
                        }
                    }

                    let mut simplified_args = vec![];
                    for arg in args {
                        if let Expression::Value(simple_expr) = arg {
                            simplified_args.push(simple_expr.clone());
                        } else {
                            let aux_var = format!("@inlined_var_{}", inlined_var_counter.next());
                            // Check if the argument is a function call to an inlined function
                            // If so, create a Line::Statement so it gets inlined in subsequent iterations
                            if let Expression::FunctionCall {
                                function_name: arg_func_name,
                                args: arg_args,
                            } = arg
                            {
                                if inlined_functions.contains_key(arg_func_name) {
                                    inlined_lines.push(Line::ForwardDeclaration { var: aux_var.clone(), mutable: false });
                                    inlined_lines.push(Line::Statement {
                                        targets: vec![AssignmentTarget::Var {
                                            var: aux_var.clone(),
                                            is_mutable: false,
                                        }],
                                        value: Expression::FunctionCall {
                                            function_name: arg_func_name.clone(),
                                            args: arg_args.clone(),
                                        },
                                        line_number: 0,
                                    });
                                } else {
                                    inlined_lines.push(Line::Statement {
                                        targets: vec![AssignmentTarget::Var {
                                            var: aux_var.clone(),
                                            is_mutable: false,
                                        }],
                                        value: arg.clone(),
                                        line_number: 0,
                                    });
                                }
                            } else {
                                inlined_lines.push(Line::Statement {
                                    targets: vec![AssignmentTarget::Var {
                                        var: aux_var.clone(),
                                        is_mutable: false,
                                    }],
                                    value: arg.clone(),
                                    line_number: 0,
                                });
                            }
                            simplified_args.push(VarOrConstMallocAccess::Var(aux_var).into());
                        }
                    }
                    assert_eq!(simplified_args.len(), func.arguments.len());
                    let inlined_args = func
                        .arguments
                        .iter()
                        .zip(&simplified_args)
                        .map(|(arg, expr)| (arg.name.clone(), expr.clone()))
                        .collect::<BTreeMap<_, _>>();
                    let mut func_body = func.body.clone();
                    inline_lines(&mut func_body, &inlined_args, targets, total_inlined_counter.next());
                    inlined_lines.extend(func_body);
                    lines_out.extend(inlined_lines);
                } else {
                    lines_out.push(line.clone());
                }
            }
            Line::Statement {
                targets,
                value,
                line_number,
            } => {
                let (value, value_lines) =
                    extract_inlined_calls_from_expr(value, inlined_functions, inlined_var_counter);
                lines_out.extend(value_lines);
                for target in targets {
                    if let AssignmentTarget::Var { var, .. } = target
                        && !ctx.defines(var)
                    {
                        ctx.add_var(var);
                    }
                }
                lines_out.push(Line::Statement {
                    targets: targets.clone(),
                    value,
                    line_number: *line_number,
                });
            }
            Line::IfCondition {
                condition,
                then_branch,
                else_branch,
                line_number,
            } => {
                extract_inlined_calls_from_condition(condition, inlined_functions, inlined_var_counter);
                ctx.scopes.push(Scope::default());
                let then_branch_out = handle_inlined_functions_helper(
                    ctx,
                    then_branch,
                    inlined_functions,
                    inlined_var_counter,
                    total_inlined_counter,
                );
                ctx.scopes.pop();
                ctx.scopes.push(Scope::default());
                let else_branch_out = handle_inlined_functions_helper(
                    ctx,
                    else_branch,
                    inlined_functions,
                    inlined_var_counter,
                    total_inlined_counter,
                );
                ctx.scopes.pop();
                lines_out.push(Line::IfCondition {
                    condition: condition.clone(),
                    then_branch: then_branch_out,
                    else_branch: else_branch_out,
                    line_number: *line_number,
                });
            }
            Line::Match { value, arms } => {
                let mut arms_out: Vec<(usize, Vec<Line>)> = Vec::new();
                for (i, arm) in arms {
                    ctx.scopes.push(Scope::default());
                    let arm_out = handle_inlined_functions_helper(
                        ctx,
                        arm,
                        inlined_functions,
                        inlined_var_counter,
                        total_inlined_counter,
                    );
                    ctx.scopes.pop();
                    arms_out.push((*i, arm_out));
                }
                lines_out.push(Line::Match {
                    value: value.clone(),
                    arms: arms_out,
                });
            }
            Line::ForwardDeclaration { var, .. } => {
                lines_out.push(line.clone());
                ctx.add_var(var);
            }
            Line::PrivateInputStart { result } => {
                lines_out.push(line.clone());
                if !ctx.defines(result) {
                    ctx.add_var(result);
                }
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
                // Handle inlining in the loop bounds
                let (start, start_lines) =
                    extract_inlined_calls_from_expr(start, inlined_functions, inlined_var_counter);
                lines_out.extend(start_lines);
                let (end, end_lines) = extract_inlined_calls_from_expr(end, inlined_functions, inlined_var_counter);
                lines_out.extend(end_lines);

                // Handle inlining in the loop body
                ctx.scopes.push(Scope::default());
                ctx.add_var(iterator);
                let loop_body_out = handle_inlined_functions_helper(
                    ctx,
                    body,
                    inlined_functions,
                    inlined_var_counter,
                    total_inlined_counter,
                );
                ctx.scopes.pop();

                // Push modified loop
                lines_out.push(Line::ForLoop {
                    iterator: iterator.clone(),
                    start,
                    end,
                    body: loop_body_out,
                    rev: *rev,
                    unroll: *unroll,
                    line_number: *line_number,
                });
            }
            Line::Assert {
                debug,
                boolean,
                line_number,
            } => {
                let (boolean, boolean_lines) =
                    extract_inlined_calls_from_boolean_expr(boolean, inlined_functions, inlined_var_counter);
                lines_out.extend(boolean_lines);
                lines_out.push(Line::Assert {
                    debug: *debug,
                    boolean,
                    line_number: *line_number,
                });
            }
            Line::Print { line_info, content } => {
                let mut new_content = vec![];
                for expr in content {
                    let (expr, expr_lines) =
                        extract_inlined_calls_from_expr(expr, inlined_functions, inlined_var_counter);
                    lines_out.extend(expr_lines);
                    new_content.push(expr);
                }
                lines_out.push(Line::Print {
                    line_info: line_info.clone(),
                    content: new_content,
                });
            }
            Line::FunctionRet { return_data } => {
                let mut new_return_data = vec![];
                for expr in return_data {
                    let (expr, expr_lines) =
                        extract_inlined_calls_from_expr(expr, inlined_functions, inlined_var_counter);
                    lines_out.extend(expr_lines);
                    new_return_data.push(expr);
                }
                lines_out.push(Line::FunctionRet {
                    return_data: new_return_data,
                });
            }
            Line::Precompile { table, args } => {
                let mut new_args = vec![];
                for expr in args {
                    let (expr, new_lines) =
                        extract_inlined_calls_from_expr(expr, inlined_functions, inlined_var_counter);
                    lines_out.extend(new_lines);
                    new_args.push(expr);
                }
                lines_out.push(Line::Precompile {
                    table: *table,
                    args: new_args,
                });
            }
            Line::MAlloc { var, size } => {
                let (size, size_lines) = extract_inlined_calls_from_expr(size, inlined_functions, inlined_var_counter);
                lines_out.extend(size_lines);

                if !ctx.defines(var) {
                    ctx.add_var(var);
                }
                lines_out.push(Line::MAlloc { var: var.clone(), size });
            }
            Line::CustomHint(hint, args) => {
                let mut new_args = vec![];
                for expr in args {
                    let (expr, new_lines) =
                        extract_inlined_calls_from_expr(expr, inlined_functions, inlined_var_counter);
                    lines_out.extend(new_lines);
                    new_args.push(expr);
                }
                lines_out.push(Line::CustomHint(*hint, new_args));
            }
        };
    }
    lines_out
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
            Line::Statement {
                targets: _,
                value: Expression::FunctionCall { function_name, args },
                line_number: _,
            } => {
                if let Some(func) = constant_functions.get(function_name.as_str()) {
                    // Check if all const arguments can be evaluated
                    let mut const_evals = Vec::new();
                    for (arg_expr, arg) in args.iter().zip(&func.arguments) {
                        if arg.is_const {
                            if let Some(const_eval) = arg_expr.naive_eval(const_arrays) {
                                const_evals.push((arg.name.clone(), const_eval));
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
                        .filter(|(_, arg)| !arg.is_const)
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
                                .filter(|arg| !arg.is_const)
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
            Line::Statement { .. } => {}
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
            SimpleExpr::Memory(VarOrConstMallocAccess::Var(var)) => {
                if let Some(const_value) = map.get(var) {
                    *value = SimpleExpr::scalar(const_value.to_usize());
                }
            }
            SimpleExpr::Memory(VarOrConstMallocAccess::ConstMallocAccess { .. }) => {
                unreachable!()
            }
            SimpleExpr::Constant(_) => {}
        },
        Expression::ArrayAccess { array, index } => {
            assert!(!map.contains_key(array), "Array {array} is a constant");
            for index in index {
                replace_vars_by_const_in_expr(index, map);
            }
        }
        Expression::MathExpr(_, args) => {
            for arg in args {
                replace_vars_by_const_in_expr(arg, map);
            }
        }
        Expression::FunctionCall { args, .. } => {
            for arg in args {
                replace_vars_by_const_in_expr(arg, map);
            }
        }
        Expression::Len { indices, .. } => {
            for idx in indices {
                replace_vars_by_const_in_expr(idx, map);
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
            Line::ForwardDeclaration { var, .. } => {
                assert!(!map.contains_key(var), "Variable {var} is a constant");
            }
            Line::Statement { targets, value, .. } => {
                replace_vars_by_const_in_expr(value, map);
                for target in targets {
                    match target {
                        AssignmentTarget::Var { var, .. } => {
                            assert!(!map.contains_key(var), "Variable {var} is a constant");
                        }
                        AssignmentTarget::ArrayAccess { array, index } => {
                            assert!(!map.contains_key(array), "Array {array} is a constant");
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
                    Condition::AssumeBoolean(expr) => {
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
            Self::AssertZero { operation, arg0, arg1 } => {
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
