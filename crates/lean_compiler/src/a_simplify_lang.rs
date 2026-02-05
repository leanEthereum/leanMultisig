use crate::{F, lang::*, parser::ConstArrayValue};
use lean_vm::{ALL_TABLES, Boolean, BooleanExpr, CustomHint, FunctionName, SourceLocation, Table, TableT};
use multilinear_toolkit::prelude::PrimeCharacteristicRing;
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::{Display, Formatter},
};
use utils::{Counter, ToUsize};

#[derive(Debug, Clone)]
pub struct SimpleProgram {
    pub functions: BTreeMap<FunctionName, SimpleFunction>,
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
        arms: Vec<Vec<Self>>,
        offset: usize, // first pattern value (arms are for offset, offset+1, ...)
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
        location: SourceLocation,
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
        location: SourceLocation,
    },
    FunctionRet {
        return_data: Vec<SimpleExpr>,
    },
    Precompile {
        table: Table,
        args: Vec<SimpleExpr>,
    },
    Panic {
        message: Option<String>,
    },
    // Hints
    /// each field element x is decomposed to: (a0, a1, a2, ..., a11, b) where:
    /// x = a0 + a1.4 + a2.4^2 + a3.4^3 + ... + a11.4^11 + b.2^24
    /// and ai < 4, b < 2^7 - 1
    /// The decomposition is unique, and always exists (except for x = -1)
    CustomHint(CustomHint, Vec<SimpleExpr>),
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
    DebugAssert(BooleanExpr<SimpleExpr>, SourceLocation),
    /// Range check: assert val <= bound
    RangeCheck {
        val: SimpleExpr,
        bound: SimpleExpr,
    },
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

    /// Returns mutable references to all nested blocks (arms of match, branches of if).
    pub fn nested_blocks_mut(&mut self) -> Vec<&mut Vec<SimpleLine>> {
        match self {
            Self::Match { arms, .. } => arms.iter_mut().collect(),
            Self::IfNotZero {
                then_branch,
                else_branch,
                ..
            } => vec![then_branch, else_branch],
            Self::ForwardDeclaration { .. }
            | Self::Assignment { .. }
            | Self::RawAccess { .. }
            | Self::AssertZero { .. }
            | Self::FunctionCall { .. }
            | Self::FunctionRet { .. }
            | Self::Precompile { .. }
            | Self::Panic { .. }
            | Self::CustomHint(..)
            | Self::Print { .. }
            | Self::HintMAlloc { .. }
            | Self::ConstMalloc { .. }
            | Self::LocationReport { .. }
            | Self::DebugAssert(..)
            | Self::RangeCheck { .. } => vec![],
        }
    }

    pub fn nested_blocks(&self) -> Vec<&Vec<SimpleLine>> {
        match self {
            Self::Match { arms, .. } => arms.iter().collect(),
            Self::IfNotZero {
                then_branch,
                else_branch,
                ..
            } => vec![then_branch, else_branch],
            Self::ForwardDeclaration { .. }
            | Self::Assignment { .. }
            | Self::RawAccess { .. }
            | Self::AssertZero { .. }
            | Self::FunctionCall { .. }
            | Self::FunctionRet { .. }
            | Self::Precompile { .. }
            | Self::Panic { .. }
            | Self::CustomHint(..)
            | Self::Print { .. }
            | Self::HintMAlloc { .. }
            | Self::ConstMalloc { .. }
            | Self::LocationReport { .. }
            | Self::DebugAssert(..)
            | Self::RangeCheck { .. } => vec![],
        }
    }
}

fn ends_with_early_exit(block: &[SimpleLine]) -> bool {
    match block.last() {
        Some(SimpleLine::Panic { .. }) | Some(SimpleLine::FunctionRet { .. }) => true,
        Some(last) => {
            let nested = last.nested_blocks();
            !nested.is_empty() && nested.iter().all(|b| ends_with_early_exit(b))
        }
        None => false,
    }
}

pub fn simplify_program(mut program: Program) -> Result<SimpleProgram, String> {
    check_program_scoping(&program);

    let mut unroll_counter = Counter::new();
    let mut inline_counter = Counter::new();
    compile_time_transform_in_program(&mut program, &mut unroll_counter, &mut inline_counter)?;

    // Remove all inlined functions (they've been inlined)
    program.functions.retain(|_, func| !func.inlined);

    validate_program_vectors(&program)?;

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

    let mut mutable_loop_counter = MutableLoopTransformCounter::default();
    transform_mutable_in_loops_in_program(&mut program, &mut mutable_loop_counter);

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
        let mut vec_tracker = VectorTracker::default();

        // Register mutable arguments and capture their initial versioned names
        // BEFORE simplifying the body
        let arguments: Vec<Var> = func
            .arguments
            .iter()
            .map(|arg| {
                assert!(!arg.is_const);
                if arg.is_mutable {
                    mut_tracker.register_mutable(&arg.name);
                    // Capture the initial versioned name (version 0)
                    mut_tracker.current_name(&arg.name)
                } else {
                    mut_tracker.assigned.insert(arg.name.clone());
                    arg.name.clone()
                }
            })
            .collect();

        let mut state = SimplifyState {
            counters: &mut counters,
            array_manager: &mut array_manager,
            mut_tracker: &mut mut_tracker,
            vec_tracker: &mut vec_tracker,
        };
        let simplified_instructions = simplify_lines(
            &ctx,
            &mut state,
            &mut const_malloc,
            &mut new_functions,
            func.n_returned_vars,
            &func.body,
            false,
        )?;
        let simplified_function = SimpleFunction {
            name: name.clone(),
            arguments,
            n_returned_vars: func.n_returned_vars,
            instructions: simplified_instructions,
        };
        check_function_always_returns(&simplified_function)?;
        new_functions.insert(name.clone(), simplified_function);
        const_malloc.map.clear();
    }
    Ok(SimpleProgram {
        functions: new_functions,
    })
}

#[derive(Debug, Clone, Default)]
pub struct VectorLenTracker {
    vectors: BTreeMap<Var, VectorLenValue>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VectorLenValue {
    Scalar,
    Vector(Vec<VectorLenValue>),
}

impl VectorLenTracker {
    fn register(&mut self, var: &Var, value: VectorLenValue) {
        self.vectors.insert(var.clone(), value);
    }

    fn is_vector(&self, var: &Var) -> bool {
        self.vectors.contains_key(var)
    }

    pub fn get(&self, var: &Var) -> Option<&VectorLenValue> {
        self.vectors.get(var)
    }

    fn get_mut(&mut self, var: &Var) -> Option<&mut VectorLenValue> {
        self.vectors.get_mut(var)
    }
}

impl VectorLenValue {
    pub fn push(&mut self, elem: Self) {
        match self {
            Self::Vector(v) => v.push(elem),
            _ => panic!("push on scalar"),
        }
    }

    pub fn pop(&mut self) -> Option<Self> {
        match self {
            Self::Vector(v) => v.pop(),
            _ => panic!("pop on scalar"),
        }
    }

    pub fn len(&self) -> usize {
        match self {
            Self::Vector(v) => v.len(),
            _ => panic!("len on scalar"),
        }
    }

    pub fn is_vector(&self) -> bool {
        matches!(self, Self::Vector(_))
    }

    fn get(&self, i: usize) -> Option<&Self> {
        match self {
            Self::Vector(v) => v.get(i),
            _ => None,
        }
    }

    fn get_mut(&mut self, i: usize) -> Option<&mut Self> {
        match self {
            Self::Vector(v) => v.get_mut(i),
            _ => None,
        }
    }

    pub fn navigate(&self, idx: &[F]) -> Option<&Self> {
        idx.iter().try_fold(self, |v, &i| v.get(i.to_usize()))
    }

    pub fn navigate_mut(&mut self, idx: &[F]) -> Option<&mut Self> {
        idx.iter().try_fold(self, |v, &i| v.get_mut(i.to_usize()))
    }
}

fn build_vector_len_value(elements: &[VecLiteral]) -> VectorLenValue {
    let mut vec_elements = Vec::new();

    for elem in elements {
        let elem_len_value = build_vector_len_value_from_element(elem);
        vec_elements.push(elem_len_value);
    }

    VectorLenValue::Vector(vec_elements)
}

fn build_vector_len_value_from_element(element: &VecLiteral) -> VectorLenValue {
    match element {
        VecLiteral::Vec(inner) => build_vector_len_value(inner),
        VecLiteral::Expr(_) => VectorLenValue::Scalar,
    }
}

fn compile_time_transform_in_program(
    program: &mut Program,
    unroll_counter: &mut Counter,
    inline_counter: &mut Counter,
) -> Result<(), String> {
    let const_arrays = program.const_arrays.clone();

    // Collect inlined functions
    let inlined_functions: BTreeMap<_, _> = program
        .functions
        .iter()
        .filter(|(_, func)| func.inlined)
        .map(|(name, func)| (name.clone(), func.clone()))
        .collect();

    for func in inlined_functions.values() {
        if func.has_mutable_arguments() {
            return Err("Inlined functions with mutable arguments are not supported yet".to_string());
        }
        if func.has_const_arguments() {
            return Err(format!(
                "Inlined function should not have \"Const\" arguments (function \"{}\")",
                func.name
            ));
        }
    }

    // Process all functions, including newly created specialized ones
    let mut processed: BTreeSet<String> = BTreeSet::new();
    loop {
        let to_process: Vec<_> = program
            .functions
            .iter()
            .filter(|(name, func)| !func.inlined && !func.has_const_arguments() && !processed.contains(*name))
            .map(|(name, _)| name.clone())
            .collect();

        if to_process.is_empty() {
            break;
        }

        let existing_functions = program.functions.clone();
        for func_name in to_process {
            processed.insert(func_name.clone());
            let func = program.functions.get_mut(&func_name).unwrap();
            let mut new_functions = BTreeMap::new();
            compile_time_transform_in_lines(
                &mut func.body,
                &const_arrays,
                &existing_functions,
                &inlined_functions,
                &mut new_functions,
                unroll_counter,
                inline_counter,
            )?;
            // Add new specialized functions - they'll be processed in the next iteration of this loop
            for (name, new_func) in new_functions {
                program.functions.entry(name).or_insert(new_func);
            }
        }
    }
    Ok(())
}

fn compile_time_transform_in_lines(
    lines: &mut Vec<Line>,
    const_arrays: &BTreeMap<String, ConstArrayValue>,
    existing_functions: &BTreeMap<String, Function>,
    inlined_functions: &BTreeMap<String, Function>,
    new_functions: &mut BTreeMap<String, Function>,
    unroll_counter: &mut Counter,
    inline_counter: &mut Counter,
) -> Result<(), String> {
    let mut vector_len_tracker = VectorLenTracker::default();
    let mut const_var_exprs: BTreeMap<Var, F> = BTreeMap::new(); // used to simplify expressions containing variables with known constant values

    let mut i = 0;
    while i < lines.len() {
        let line = &mut lines[i];

        // Handle match_range expansion FIRST, before any expression transformations
        // This is necessary because lambda bodies contain bound variables that don't exist in scope
        if let Line::Statement {
            targets,
            value,
            location,
        } = line
            && let Some(expanded) = try_expand_match_range(value, targets, *location)?
        {
            lines.splice(i..=i, expanded);
            continue;
        }

        for expr in line.expressions_mut() {
            substitute_const_vars_in_expr(expr, &const_var_exprs);
            compile_time_transform_in_expr(expr, const_arrays, &vector_len_tracker);
        }

        // Extract nested calls to functions requiring preprocessing (inlined or const-arg)
        // e.g., `x = a + inlined_func(b)` -> `tmp = inlined_func(b); x = a + tmp`
        if let Some(new_lines) =
            extract_preprocessed_calls(line, inlined_functions, existing_functions, inline_counter)?
        {
            lines.splice(i..=i, new_lines);
            continue;
        }

        match line {
            Line::Statement { targets, value, .. } => {
                if let Some(inlined) = try_inline_call(value, targets, inlined_functions, const_arrays, inline_counter)
                {
                    lines.splice(i..=i, inlined);
                    continue;
                }
                // Handle direct const-arg function calls: specialize them (e.g., double(1) -> double_a=1())
                if let Expression::FunctionCall {
                    function_name, args, ..
                } = value
                    && let Some(func) = existing_functions.get(function_name.as_str())
                    && func.has_const_arguments()
                {
                    let mut const_evals = Vec::new();
                    for (arg_expr, arg) in args.iter().zip(&func.arguments) {
                        if arg.is_const {
                            if let Some(const_eval) = arg_expr.as_scalar() {
                                const_evals.push((arg.name.clone(), const_eval));
                            } else {
                                return Err(format!(
                                    "Cannot evaluate const argument '{}' for function '{}'",
                                    arg.name, function_name
                                ));
                            }
                        }
                    }
                    let const_funct_name = format!(
                        "{function_name}_{}",
                        const_evals
                            .iter()
                            .map(|(v, c)| format!("{v}={c}"))
                            .collect::<Vec<_>>()
                            .join("_")
                    );
                    *function_name = const_funct_name.clone();
                    *args = args
                        .iter()
                        .zip(&func.arguments)
                        .filter(|(_, arg)| !arg.is_const)
                        .map(|(e, _)| e.clone())
                        .collect();
                    if !new_functions.contains_key(&const_funct_name)
                        && !existing_functions.contains_key(&const_funct_name)
                    {
                        let mut new_body = func.body.clone();
                        replace_vars_by_const_in_lines(&mut new_body, &const_evals.iter().cloned().collect());
                        new_functions.insert(
                            const_funct_name.clone(),
                            Function {
                                name: const_funct_name,
                                arguments: func.arguments.iter().filter(|a| !a.is_const).cloned().collect(),
                                inlined: false,
                                body: new_body,
                                n_returned_vars: func.n_returned_vars,
                            },
                        );
                    }
                }
                if targets.len() == 1
                    && let AssignmentTarget::Var { var, is_mutable: false } = &targets[0]
                    && let Some(value_const) = value.as_scalar()
                {
                    const_var_exprs.insert(var.clone(), value_const);
                }
            }

            Line::VecDeclaration { var, elements, .. } => {
                vector_len_tracker.register(var, build_vector_len_value(elements));
            }

            Line::Push {
                vector,
                indices,
                element,
                ..
            } => {
                let Some(const_indices) = indices.iter().map(|idx| idx.as_scalar()).collect::<Option<Vec<_>>>() else {
                    return Err("push with non-constant indices".to_string());
                };
                let new_element = build_vector_len_value_from_element(element);
                let vector_value = vector_len_tracker
                    .get_mut(vector)
                    .ok_or_else(|| "pushing to undeclared vector".to_string())?;
                if const_indices.is_empty() {
                    vector_value.push(new_element);
                } else {
                    let target = vector_value
                        .navigate_mut(&const_indices)
                        .ok_or_else(|| "push target index out of bounds".to_string())?;
                    if !target.is_vector() {
                        return Err("push target is not a vector".to_string());
                    }
                    target.push(new_element);
                }
            }

            Line::Pop {
                vector,
                indices,
                location,
            } => {
                let Some(const_indices) = indices.iter().map(|idx| idx.as_scalar()).collect::<Option<Vec<_>>>() else {
                    return Err(format!("line {}: pop with non-constant indices", location));
                };
                let vector_value = vector_len_tracker
                    .get_mut(vector)
                    .ok_or_else(|| format!("line {}: pop on undeclared vector '{}'", location, vector))?;
                if const_indices.is_empty() {
                    if vector_value.len() == 0 {
                        return Err(format!("line {}: pop on empty vector '{}'", location, vector));
                    }
                    vector_value.pop();
                } else {
                    let target = vector_value
                        .navigate_mut(&const_indices)
                        .ok_or_else(|| format!("line {}: pop target index out of bounds", location))?;
                    if !target.is_vector() {
                        return Err(format!("line {}: pop target is not a vector", location));
                    }
                    if target.len() == 0 {
                        return Err(format!("line {}: pop on empty vector", location));
                    }
                    target.pop();
                }
            }

            Line::IfCondition {
                condition,
                then_branch,
                else_branch,
                ..
            } => {
                if let Some(constant_condition) = condition.eval_with(&|expr| expr.as_scalar()) {
                    let chosen_branch = if constant_condition { then_branch } else { else_branch }.clone();
                    lines.splice(i..=i, chosen_branch);
                    continue;
                }
            }

            Line::ForLoop {
                iterator,
                start,
                end,
                body,
                unroll: true,
                ..
            } => {
                let (Some(start), Some(end)) = (start.as_scalar(), end.as_scalar()) else {
                    return Err("Cannot unroll loop with non-constant bounds".to_string());
                };
                let unroll_index = unroll_counter.get_next();
                let (internal_vars, _) = find_variable_usage(body, const_arrays);
                let iterator = iterator.clone();
                let body = body.clone();
                let mut unrolled = Vec::new();
                for j in start.to_usize()..end.to_usize() {
                    let mut body_copy = body.clone();
                    replace_vars_for_unroll(&mut body_copy, &iterator, unroll_index, j, &internal_vars);
                    unrolled.extend(body_copy);
                }
                lines.splice(i..=i, unrolled);
                continue;
            }
            _ => {}
        }

        for block in lines[i].nested_blocks_mut() {
            compile_time_transform_in_lines(
                block,
                const_arrays,
                existing_functions,
                inlined_functions,
                new_functions,
                unroll_counter,
                inline_counter,
            )?;
        }
        i += 1;
    }
    Ok(())
}

/// Expand match_range(value, range(a,b), lambda, ...) into forward declarations + Line::Match
///
/// match_range(value, range(a, b), lambda i: expr1, range(b, c), lambda i: expr2, ...)
fn try_expand_match_range(
    value: &Expression,
    targets: &[AssignmentTarget],
    location: SourceLocation,
) -> Result<Option<Vec<Line>>, String> {
    let Expression::FunctionCall {
        function_name, args, ..
    } = value
    else {
        return Ok(None);
    };
    if function_name != "match_range" {
        return Ok(None);
    }
    if args.len() < 3 || (args.len() - 1) % 2 != 0 {
        return Err("match_range expects: value, range, lambda, range, lambda, ...".to_string());
    }

    // Check that user didn't explicitly request mutable results
    for t in targets {
        if let AssignmentTarget::Var { var, is_mutable: true } = t {
            return Err(format!(
                "match_range results are always immutable, cannot use ': Mut' for '{var}'"
            ));
        }
    }

    // Generate forward declarations for variable targets (always immutable)
    let mut result = vec![];
    let arm_targets: Vec<_> = targets
        .iter()
        .map(|t| match t {
            AssignmentTarget::Var { var, .. } => {
                result.push(Line::ForwardDeclaration {
                    var: var.clone(),
                    is_mutable: false,
                });
                AssignmentTarget::Var {
                    var: var.clone(),
                    is_mutable: false,
                }
            }
            other => other.clone(),
        })
        .collect();

    // Parse range/lambda pairs and build match arms
    let mut arms = vec![];
    let mut expected_start: Option<usize> = None;

    for (range_arg, lambda_arg) in args[1..].chunks(2).map(|c| (&c[0], &c[1])) {
        // Parse range(start, end)
        let Expression::FunctionCall {
            function_name: rf,
            args: ra,
            ..
        } = range_arg
        else {
            return Err("match_range: expected range(start, end)".into());
        };
        if rf != "range" || ra.len() != 2 {
            return Err("match_range: expected range(start, end)".into());
        }
        let start = ra[0]
            .as_scalar()
            .ok_or("match_range: range start must be constant")?
            .to_usize();
        let end = ra[1]
            .as_scalar()
            .ok_or("match_range: range end must be constant")?
            .to_usize();

        // Parse lambda
        let Expression::Lambda { param, body } = lambda_arg else {
            return Err("match_range: expected lambda".into());
        };

        // Check ranges are continuous
        if let Some(exp) = expected_start
            && start != exp
        {
            return Err(format!(
                "match_range: ranges must be continuous, expected start {exp} but got {start}"
            ));
        }
        expected_start = Some(end);

        for case_val in start..end {
            let mut expr = body.as_ref().clone();
            substitute_lambda_param(&mut expr, param, case_val);
            arms.push((
                case_val,
                vec![Line::Statement {
                    targets: arm_targets.clone(),
                    value: expr,
                    location,
                }],
            ));
        }
    }

    result.push(Line::Match {
        value: args[0].clone(),
        arms,
        location,
    });
    Ok(Some(result))
}

/// Substitute lambda parameter with a constant value
fn substitute_lambda_param(expr: &mut Expression, param: &str, value: usize) {
    if let Expression::Value(SimpleExpr::Memory(VarOrConstMallocAccess::Var(v))) = expr
        && v == param
    {
        *expr = Expression::scalar(F::from_usize(value));
        return;
    }
    for inner in expr.inner_exprs_mut() {
        substitute_lambda_param(inner, param, value);
    }
}

/// Try to inline a function call. Returns Some(inlined_lines) if successful.
fn try_inline_call(
    value: &Expression,
    targets: &[AssignmentTarget],
    inlined_functions: &BTreeMap<String, Function>,
    const_arrays: &BTreeMap<String, ConstArrayValue>,
    inline_counter: &mut Counter,
) -> Option<Vec<Line>> {
    let Expression::FunctionCall {
        function_name,
        args,
        location,
    } = value
    else {
        return None;
    };
    let func = inlined_functions.get(function_name)?;

    // If any arg is not simple, extract it first
    if args.iter().any(|a| !matches!(a, Expression::Value(_))) {
        let mut new_lines = vec![];
        let mut new_args = vec![];
        for arg in args {
            if let Expression::Value(v) = arg {
                new_args.push(Expression::Value(v.clone()));
            } else {
                let tmp = format!("@inline_arg_{}", inline_counter.get_next());
                new_lines.push(Line::ForwardDeclaration {
                    var: tmp.clone(),
                    is_mutable: false,
                });
                new_lines.push(Line::Statement {
                    targets: vec![AssignmentTarget::Var {
                        var: tmp.clone(),
                        is_mutable: false,
                    }],
                    value: arg.clone(),
                    location: *location,
                });
                new_args.push(Expression::var(tmp));
            }
        }
        new_lines.push(Line::Statement {
            targets: targets.to_vec(),
            value: Expression::FunctionCall {
                function_name: function_name.clone(),
                args: new_args,
                location: *location,
            },
            location: *location,
        });
        return Some(new_lines);
    }

    // All args are simple - inline the function body
    let args_map: BTreeMap<Var, SimpleExpr> = func
        .arguments
        .iter()
        .zip(args)
        .map(|(arg, expr)| {
            let Expression::Value(v) = expr else { unreachable!() };
            (arg.name.clone(), v.clone())
        })
        .collect();

    let mut body = func.body.clone();
    inline_lines(&mut body, &args_map, const_arrays, targets, inline_counter.get_next());
    Some(body)
}

/// Extract nested calls to functions that need preprocessing (inlined or const-arg).
/// Replaces them with temp vars so they become direct calls that can be processed.
fn extract_preprocessed_calls(
    line: &mut Line,
    inlined_functions: &BTreeMap<String, Function>,
    all_functions: &BTreeMap<String, Function>,
    counter: &mut Counter,
) -> Result<Option<Vec<Line>>, String> {
    fn needs_preprocessing(name: &str, inlined: &BTreeMap<String, Function>, all: &BTreeMap<String, Function>) -> bool {
        inlined.contains_key(name) || all.get(name).is_some_and(|f| f.has_const_arguments())
    }

    fn extract(
        expr: &mut Expression,
        inlined: &BTreeMap<String, Function>,
        all: &BTreeMap<String, Function>,
        counter: &mut Counter,
        out: &mut Vec<Line>,
    ) -> Result<(), String> {
        for inner in expr.inner_exprs_mut() {
            extract(inner, inlined, all, counter, out)?;
        }
        if let Expression::FunctionCall {
            function_name,
            args,
            location,
        } = expr
            && needs_preprocessing(function_name, inlined, all)
        {
            let func = inlined.get(function_name).or_else(|| all.get(function_name));
            if let Some(f) = func
                && f.n_returned_vars != 1
            {
                return Err(format!(
                    "Function '{}' with {} return values cannot appear in expression",
                    function_name, f.n_returned_vars
                ));
            }
            let tmp = format!("@extract_tmp_{}", counter.get_next());
            out.push(Line::ForwardDeclaration {
                var: tmp.clone(),
                is_mutable: false,
            });
            out.push(Line::Statement {
                targets: vec![AssignmentTarget::Var {
                    var: tmp.clone(),
                    is_mutable: false,
                }],
                value: Expression::FunctionCall {
                    function_name: function_name.clone(),
                    args: args.clone(),
                    location: *location,
                },
                location: *location,
            });
            *expr = Expression::var(tmp);
        }
        Ok(())
    }

    let mut extractions = vec![];
    // For direct preprocessed calls, only extract from arguments; otherwise extract from all expressions
    match line {
        Line::Statement {
            value: Expression::FunctionCall {
                function_name, args, ..
            },
            ..
        } if needs_preprocessing(function_name, inlined_functions, all_functions) => {
            for arg in args.iter_mut() {
                extract(arg, inlined_functions, all_functions, counter, &mut extractions)?;
            }
        }
        _ => {
            for expr in line.expressions_mut() {
                extract(expr, inlined_functions, all_functions, counter, &mut extractions)?;
            }
        }
    }

    if extractions.is_empty() {
        Ok(None)
    } else {
        extractions.push(line.clone());
        Ok(Some(extractions))
    }
}

fn compile_time_transform_in_expr(
    expr: &mut Expression,
    const_arrays: &BTreeMap<String, ConstArrayValue>,
    vector_len_tracker: &VectorLenTracker,
) -> bool {
    if expr.is_scalar() {
        return false;
    }
    let mut changed = false;
    for inner_expr in expr.inner_exprs_mut() {
        changed |= compile_time_transform_in_expr(inner_expr, const_arrays, vector_len_tracker);
    }
    if let Some(scalar) = expr.compile_time_eval(const_arrays, vector_len_tracker) {
        *expr = Expression::scalar(scalar);
        changed = true;
    }
    changed
}

fn substitute_const_vars_in_expr(expr: &mut Expression, const_var_exprs: &BTreeMap<Var, F>) -> bool {
    if let Expression::Value(SimpleExpr::Memory(VarOrConstMallocAccess::Var(var))) = expr
        && let Some(replacement) = const_var_exprs.get(var)
    {
        *expr = Expression::scalar(*replacement);
        return true;
    }

    let mut changed = false;
    for inner in expr.inner_exprs_mut() {
        changed |= substitute_const_vars_in_expr(inner, const_var_exprs);
    }
    changed
}

// ============================================================================
// TRANSFORMATION: Mutable variables in non-unrolled loops
// ============================================================================
//
// This transformation handles mutable variables that are modified inside
// non-unrolled loops by using buffers to store intermediate values.
//
// For a loop like:
//   for i in start..end { x += i; }
//
// We transform it to:
//   size = end - start;
//   x_buff = Array(size + 1);
//   x_buff[0] = x;
//   for i in start..end {
//       buff_idx = i - start;
//       mut x_body = x_buff[buff_idx];
//       x_body += i;
//       x_buff[buff_idx + 1] = x_body;
//   }
//   x = x_buff[size];

/// Counter for generating unique variable names in the mutable loop transformation
#[derive(Default)]
struct MutableLoopTransformCounter {
    counter: usize,
}

impl MutableLoopTransformCounter {
    fn next_suffix(&mut self) -> usize {
        let c = self.counter;
        self.counter += 1;
        c
    }
}

/// Finds mutable variables that are:
/// 1. Defined OUTSIDE this block (external)
/// 2. Re-assigned INSIDE this block
fn find_modified_external_vars(lines: &[Line], const_arrays: &BTreeMap<String, ConstArrayValue>) -> BTreeSet<Var> {
    // Use the existing find_variable_usage to get external variables
    // (variables that are read but not defined in this block)
    let (internal_vars, external_vars) = find_variable_usage(lines, const_arrays);

    // Now find which external variables are assigned to (modified)
    let mut modified_external_vars = BTreeSet::new();
    find_assigned_external_vars_helper(
        lines,
        const_arrays,
        &internal_vars,
        &external_vars,
        &mut modified_external_vars,
    );

    modified_external_vars
}

/// Helper to find external variables that are assigned to inside a block.
fn find_assigned_external_vars_helper(
    lines: &[Line],
    const_arrays: &BTreeMap<String, ConstArrayValue>,
    internal_vars: &BTreeSet<Var>,
    external_vars: &BTreeSet<Var>,
    modified_external_vars: &mut BTreeSet<Var>,
) {
    for line in lines {
        match line {
            Line::Statement { targets, .. } => {
                for target in targets {
                    if let AssignmentTarget::Var { var, is_mutable } = target {
                        // Only non-mutable assignments can be modifications
                        // (is_mutable: true means it's the initial declaration)
                        if !*is_mutable
                            && external_vars.contains(var)
                            && !internal_vars.contains(var)
                            && !const_arrays.contains_key(var)
                        {
                            modified_external_vars.insert(var.clone());
                        }
                    }
                }
            }
            _ => {
                for block in line.nested_blocks() {
                    find_assigned_external_vars_helper(
                        block,
                        const_arrays,
                        internal_vars,
                        external_vars,
                        modified_external_vars,
                    );
                }
            }
        }
    }
}

fn transform_mutable_in_loops_in_program(program: &mut Program, counter: &mut MutableLoopTransformCounter) {
    for func in program.functions.values_mut() {
        transform_mutable_in_loops_in_lines(&mut func.body, &program.const_arrays, counter);
    }
}

fn transform_mutable_in_loops_in_lines(
    lines: &mut Vec<Line>,
    const_arrays: &BTreeMap<String, ConstArrayValue>,
    counter: &mut MutableLoopTransformCounter,
) {
    let mut i = 0;
    while i < lines.len() {
        match &mut lines[i] {
            Line::ForLoop { body, unroll: true, .. } => {
                transform_mutable_in_loops_in_lines(body, const_arrays, counter);
                i += 1;
            }
            Line::ForLoop {
                iterator,
                start,
                end,
                body,
                unroll: false,
                location,
            } => {
                transform_mutable_in_loops_in_lines(body, const_arrays, counter);
                let modified_vars = find_modified_external_vars(body, const_arrays);

                if modified_vars.is_empty() {
                    // No mutable variables modified, no transformation needed
                    i += 1;
                    continue;
                }

                let suffix = counter.next_suffix();

                // Generate the transformed code
                let mut new_lines = Vec::new();

                let location = *location;

                // Create size variable: @loop_size_{suffix} = end - start
                // TODO opti if start is zero
                let size_var = format!("@loop_size_{suffix}");
                new_lines.push(Line::Statement {
                    targets: vec![AssignmentTarget::Var {
                        var: size_var.clone(),
                        is_mutable: false,
                    }],
                    value: Expression::MathExpr(MathOperation::Sub, vec![end.clone(), start.clone()]),
                    location,
                });

                let mut var_to_buff: BTreeMap<Var, (Var, Var)> = BTreeMap::new(); // var -> (buff_name, body_name)

                for var in &modified_vars {
                    let buff_name = format!("@loop_buff_{var}_{suffix}");
                    let body_name = format!("@loop_body_{var}_{suffix}");

                    // buff = Array(size + 1)
                    new_lines.push(Line::Statement {
                        targets: vec![AssignmentTarget::Var {
                            var: buff_name.clone(),
                            is_mutable: false,
                        }],
                        value: Expression::FunctionCall {
                            function_name: "Array".to_string(),
                            args: vec![Expression::MathExpr(
                                // TODO opti in case there is only one mutated var
                                MathOperation::Add,
                                vec![Expression::var(size_var.clone()), Expression::one()],
                            )],
                            location,
                        },
                        location,
                    });

                    // buff[0] = var (current value)
                    new_lines.push(Line::Statement {
                        targets: vec![AssignmentTarget::ArrayAccess {
                            array: buff_name.clone(),
                            index: Box::new(Expression::zero()),
                        }],
                        value: Expression::var(var.clone()),
                        location,
                    });

                    var_to_buff.insert(var.clone(), (buff_name, body_name));
                }

                // Transform the loop body
                let iterator = iterator.clone();
                let mut new_body = Vec::new();

                // buff_idx = i - start
                let buff_idx_var = format!("@loop_buff_idx_{suffix}");
                new_body.push(Line::Statement {
                    targets: vec![AssignmentTarget::Var {
                        var: buff_idx_var.clone(),
                        is_mutable: false,
                    }],
                    value: Expression::MathExpr(
                        MathOperation::Sub,
                        vec![Expression::var(iterator.clone()), start.clone()], // TODO opti if start is zero
                    ),
                    location,
                });

                // For each modified variable: mut body_var = buff[buff_idx]
                for (var, (buff_name, body_name)) in &var_to_buff {
                    new_body.push(Line::Statement {
                        targets: vec![AssignmentTarget::Var {
                            var: body_name.clone(),
                            is_mutable: true,
                        }],
                        value: Expression::ArrayAccess {
                            array: buff_name.clone(),
                            index: vec![Expression::Value(
                                VarOrConstMallocAccess::Var(buff_idx_var.clone()).into(),
                            )],
                        },
                        location,
                    });

                    // Replace all references to var with body_name in the original body
                    replace_var_in_lines(body, var, body_name);
                }

                // Add the original body (now modified to use body_vars)
                new_body.append(body);

                // next_idx = buff_idx + 1
                let next_idx_var = format!("@loop_next_idx_{suffix}");
                new_body.push(Line::Statement {
                    targets: vec![AssignmentTarget::Var {
                        var: next_idx_var.clone(),
                        is_mutable: false,
                    }],
                    value: Expression::MathExpr(
                        MathOperation::Add,
                        vec![Expression::var(buff_idx_var.clone()), Expression::one()],
                    ),
                    location,
                });

                // For each modified variable: buff[next_idx] = body_var
                for (buff_name, body_name) in var_to_buff.values() {
                    new_body.push(Line::Statement {
                        targets: vec![AssignmentTarget::ArrayAccess {
                            array: buff_name.clone(),
                            index: Expression::var(next_idx_var.clone()).into(),
                        }],
                        value: Expression::var(body_name.clone()),
                        location,
                    });
                }

                // Create the new loop
                new_lines.push(Line::ForLoop {
                    iterator: iterator.clone(),
                    start: start.clone(),
                    end: end.clone(),
                    body: new_body,
                    unroll: false,
                    location,
                });

                // After the loop: var = buff[size]
                for (var, (buff_name, _body_name)) in &var_to_buff {
                    new_lines.push(Line::Statement {
                        targets: vec![AssignmentTarget::Var {
                            var: var.clone(),
                            is_mutable: false,
                        }],
                        value: Expression::ArrayAccess {
                            array: buff_name.clone(),
                            index: vec![Expression::var(size_var.clone())],
                        },
                        location,
                    });
                }

                // Replace the original loop with the new lines
                let num_new = new_lines.len();
                lines.splice(i..=i, new_lines);
                i += num_new;
            }
            line @ (Line::IfCondition { .. } | Line::Match { .. }) => {
                for block in line.nested_blocks_mut() {
                    transform_mutable_in_loops_in_lines(block, const_arrays, counter);
                }
                i += 1;
            }
            _ => {
                i += 1;
            }
        }
    }
}

/// Replaces all occurrences of a variable with another variable in a list of lines.
/// This is used to replace references to mutable variables with their body counterparts.
fn replace_var_in_lines(lines: &mut [Line], old_var: &Var, new_var: &Var) {
    for line in lines {
        match line {
            Line::ForwardDeclaration { var, .. } => {
                if var == old_var {
                    *var = new_var.clone();
                }
            }
            Line::Statement { targets, .. } => {
                for target in targets {
                    match target {
                        AssignmentTarget::Var { var, .. } => {
                            if var == old_var {
                                *var = new_var.clone();
                            }
                        }
                        AssignmentTarget::ArrayAccess { array, index } => {
                            if array == old_var {
                                *array = new_var.clone();
                            }
                            replace_var_in_expr(index, old_var, new_var);
                        }
                    }
                }
            }
            _ => {}
        }
        for expr in line.expressions_mut() {
            replace_var_in_expr(expr, old_var, new_var);
        }
        for block in line.nested_blocks_mut() {
            replace_var_in_lines(block, old_var, new_var);
        }
    }
}

fn replace_var_in_expr(expr: &mut Expression, old_var: &Var, new_var: &Var) {
    match expr {
        Expression::Value(simple_expr) => {
            if let SimpleExpr::Memory(VarOrConstMallocAccess::Var(var)) = simple_expr
                && var == old_var
            {
                *var = new_var.clone();
            }
        }
        Expression::ArrayAccess { array, .. } => {
            if array == old_var {
                *array = new_var.clone();
            }
        }
        _ => {}
    }
    for inner_expr in expr.inner_exprs_mut() {
        replace_var_in_expr(inner_expr, old_var, new_var);
    }
}

fn check_function_always_returns(func: &SimpleFunction) -> Result<(), String> {
    check_block_always_returns(&func.name, &func.instructions)
}

fn check_block_always_returns(function_name: &String, instructions: &[SimpleLine]) -> Result<(), String> {
    if let Some(last_instruction) = instructions.last() {
        if matches!(
            last_instruction,
            SimpleLine::FunctionRet { return_data: _ } | SimpleLine::Panic { .. }
        ) {
            return Ok(());
        }
        let inner_blocks = last_instruction.nested_blocks();
        if !inner_blocks.is_empty() {
            for block in inner_blocks {
                check_block_always_returns(function_name, block)?;
            }
            return Ok(());
        }
    }
    Err(format!("Cannot prove that function always returns: {function_name}"))
}

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

fn check_block_scoping(block: &[Line], ctx: &mut Context) {
    for line in block.iter() {
        match line {
            Line::ForwardDeclaration { var, .. } => {
                ctx.add_var(var);
            }
            Line::Match { value, arms, .. } => {
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
                location: _,
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
                unroll: _,
                location: _,
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
            Line::Panic { .. } | Line::LocationReport { .. } => {}
            Line::VecDeclaration { var, elements, .. } => {
                // Check expressions in vec elements
                check_vec_literal_scoping(elements, ctx);
                // Add the vector variable to scope
                ctx.add_var(var);
            }
            Line::Push {
                vector,
                indices,
                element,
                ..
            } => {
                // Check the vector variable is in scope
                assert!(ctx.defines(vector), "Vector variable '{}' not in scope", vector);
                // Check indices are in scope
                for idx in indices {
                    check_expr_scoping(idx, ctx);
                }
                // Check the pushed element
                check_vec_literal_element_scoping(element, ctx);
            }
            Line::Pop { vector, indices, .. } => {
                // Check the vector variable is in scope
                assert!(ctx.defines(vector), "Vector variable '{}' not in scope", vector);
                // Check indices are in scope
                for idx in indices {
                    check_expr_scoping(idx, ctx);
                }
            }
        }
    }
}

fn validate_program_vectors(program: &Program) -> Result<(), String> {
    let inlined_functions = program.inlined_function_names();
    for f in program.functions.values() {
        validate_vectors(&f.body, &BTreeSet::new(), &inlined_functions, None)?;
    }
    Ok(())
}

fn validate_vectors(
    lines: &[Line],
    outer: &BTreeSet<Var>,
    inlined: &BTreeSet<String>,
    restrict: Option<SourceLocation>,
) -> Result<(), String> {
    let mut local: BTreeSet<Var> = BTreeSet::new();
    macro_rules! all {
        () => {
            outer.union(&local).cloned().collect::<BTreeSet<Var>>()
        };
    }

    for line in lines {
        match line {
            Line::VecDeclaration { var, elements, .. } => {
                local.insert(var.clone());
                validate_vec_lit(elements, &all!(), inlined)?;
            }
            Line::Push {
                vector,
                element,
                location,
                ..
            } => {
                if restrict.is_some() && outer.contains(vector) {
                    return Err(format!("line {}: push to outer-scope vector '{}'", location, vector));
                }
                validate_vec_lit(std::slice::from_ref(element), &all!(), inlined)?;
                if !local.contains(vector) && !outer.contains(vector) {
                    return Err(format!("line {}: unknown vector '{}'", location, vector));
                }
            }
            Line::Pop { vector, location, .. } => {
                if restrict.is_some() && outer.contains(vector) {
                    return Err(format!("line {}: pop from outer-scope vector '{}'", location, vector));
                }
                if !local.contains(vector) && !outer.contains(vector) {
                    return Err(format!("line {}: unknown vector '{}'", location, vector));
                }
            }
            Line::Statement { value, .. } => {
                check_vec_in_call(value, &all!(), inlined)?;
            }
            Line::IfCondition {
                then_branch,
                else_branch,
                location,
                ..
            } => {
                validate_vectors(then_branch, &all!(), inlined, Some(*location))?;
                validate_vectors(else_branch, &all!(), inlined, Some(*location))?;
            }
            Line::ForLoop {
                body, unroll, location, ..
            } => {
                validate_vectors(body, &all!(), inlined, if *unroll { None } else { Some(*location) })?;
            }
            Line::Match { arms, location, .. } => {
                for (_, arm) in arms {
                    validate_vectors(arm, &all!(), inlined, Some(*location))?;
                }
            }
            _ => {}
        }
    }
    Ok(())
}

fn validate_vec_lit(elems: &[VecLiteral], vecs: &BTreeSet<Var>, inlined: &BTreeSet<String>) -> Result<(), String> {
    for e in elems {
        match e {
            VecLiteral::Expr(expr) => check_vec_in_call(expr, vecs, inlined)?,
            VecLiteral::Vec(inner) => validate_vec_lit(inner, vecs, inlined)?,
        }
    }
    Ok(())
}

fn check_vec_in_call(expr: &Expression, vecs: &BTreeSet<Var>, inlined: &BTreeSet<String>) -> Result<(), String> {
    if let Expression::FunctionCall {
        function_name,
        args,
        location,
    } = expr
        && !inlined.contains(function_name)
    {
        for arg in args {
            if let Expression::Value(SimpleExpr::Memory(VarOrConstMallocAccess::Var(v))) = arg
                && vecs.contains(v)
            {
                return Err(format!(
                    "line {}: vector '{}' passed to function '{}'",
                    location, v, function_name
                ));
            }
        }
    }
    Ok(())
}

fn check_vec_literal_scoping(elements: &[VecLiteral], ctx: &Context) {
    for elem in elements {
        check_vec_literal_element_scoping(elem, ctx);
    }
}

fn check_vec_literal_element_scoping(elem: &VecLiteral, ctx: &Context) {
    match elem {
        VecLiteral::Expr(expr) => check_expr_scoping(expr, ctx),
        VecLiteral::Vec(inner) => check_vec_literal_scoping(inner, ctx),
    }
}

fn check_expr_scoping(expr: &Expression, ctx: &Context) {
    match expr {
        Expression::Value(simple_expr) => {
            check_simple_expr_scoping(simple_expr, ctx);
        }
        Expression::Lambda { param, body } => {
            // Lambda parameters are in scope within the body
            let mut lambda_ctx = Context::new();
            lambda_ctx.scopes = ctx.scopes.clone();
            lambda_ctx.const_arrays = ctx.const_arrays.clone();
            lambda_ctx.add_var(param);
            check_expr_scoping(body, &lambda_ctx);
        }
        _ => {
            for inner_expr in expr.inner_exprs() {
                check_expr_scoping(inner_expr, ctx);
            }
        }
    }
}

fn check_simple_expr_scoping(expr: &SimpleExpr, ctx: &Context) {
    match expr {
        SimpleExpr::Memory(VarOrConstMallocAccess::Var(v)) => {
            assert!(ctx.defines(v), "Variable used but not defined: {v}");
        }
        SimpleExpr::Memory(VarOrConstMallocAccess::ConstMallocAccess { .. }) | SimpleExpr::Constant(_) => {}
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
    aux_vars: Counter,
    loops: Counter,
}

impl Counters {
    fn aux_var(&mut self) -> Var {
        let var = format!("@aux_var_{}", self.aux_vars.get_next());
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
    vec_tracker: &'a mut VectorTracker,
}

#[derive(Debug, Clone, Default)]
struct ArrayManager {
    counter: usize,
    aux_vars: BTreeMap<(Var, Expression), Var>, // (array, index) -> aux_var
    valid: BTreeSet<Var>,                       // currently valid aux vars
}

/// Tracks the current "version" of each mutable variable for SSA-like transformation
#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct MutableVarTracker {
    /// For mutable variables: maps original variable name -> current version number (0 = original)
    versions: BTreeMap<Var, usize>,
    /// Tracks assigned immutable variables to detect illegal reassignment
    assigned: BTreeSet<Var>,
}

impl MutableVarTracker {
    fn is_mutable(&self, var: &Var) -> bool {
        self.versions.contains_key(var)
    }

    fn register_mutable(&mut self, var: &Var) {
        self.versions.insert(var.clone(), 0);
    }

    fn current_name(&self, var: &Var) -> Var {
        if self.is_mutable(var) {
            format!("@mut_{var}_{}", self.versions.get(var).copied().unwrap_or(0))
        } else {
            var.clone()
        }
    }

    fn current_version(&self, var: &Var) -> usize {
        self.versions.get(var).copied().unwrap_or(0)
    }

    fn increment_version(&mut self, var: &Var) -> Var {
        let version = self.versions.entry(var.clone()).or_insert(0);
        *version += 1;
        format!("@mut_{var}_{version}")
    }

    fn check_immutable_assignment(&mut self, var: &Var) -> Result<(), String> {
        if var.starts_with('@') || self.assigned.insert(var.clone()) {
            Ok(())
        } else {
            Err(format!(
                "Cannot reassign immutable variable '{var}'. Use '{var}: Mut' for mutable variables, or 'assert {var} == <value>;' to check equality"
            ))
        }
    }

    /// Unifies mutable variable versions across multiple branches.
    /// Returns forward declarations to add before the branching construct.
    fn unify_branch_versions(
        &mut self,
        snapshot_versions: &BTreeMap<Var, usize>,
        branch_versions: &[BTreeMap<Var, usize>],
        branches: &mut [Vec<SimpleLine>],
    ) -> Vec<SimpleLine> {
        let mut forward_decls = Vec::new();

        let branch_exits_early: Vec<bool> = branches.iter().map(|b| ends_with_early_exit(b)).collect();

        // Collect variables that were newly introduced in branches (not in snapshot)
        let mut branch_local_vars = Vec::new();

        for var in self.versions.clone().keys() {
            let was_in_snapshot = snapshot_versions.contains_key(var);
            let snapshot_v = snapshot_versions.get(var).copied().unwrap_or(0);

            // Check which continuing branches have this variable
            let branch_has_var: Vec<bool> = branch_versions.iter().map(|v| v.contains_key(var)).collect();
            let versions: Vec<usize> = branch_versions
                .iter()
                .map(|v| v.get(var).copied().unwrap_or(0))
                .collect();

            // Only consider versions from branches that don't exit early for unification
            let continuing_branches: Vec<(usize, bool, usize)> = versions
                .iter()
                .zip(branch_exits_early.iter())
                .zip(branch_has_var.iter())
                .enumerate()
                .filter(|(_, ((_, exits), _))| !*exits)
                .map(|(idx, ((v, _), has))| (idx, *has, *v))
                .collect();

            // If all branches exit early, no unification needed - just keep the snapshot version
            if continuing_branches.is_empty() {
                self.versions.insert(var.clone(), snapshot_v);
                continue;
            }

            // If variable wasn't in snapshot, check if it exists in all continuing branches
            if !was_in_snapshot {
                let exists_in_all = continuing_branches.iter().all(|(_, has, _)| *has);
                if !exists_in_all {
                    // Variable was introduced in some branches but not all - it's branch-local
                    // Don't unify; remove from tracker after processing
                    branch_local_vars.push(var.clone());
                    continue;
                }
            }

            let continuing_versions: Vec<usize> = continuing_branches.iter().map(|(_, _, v)| *v).collect();

            // Check if all continuing branches have the same version
            if continuing_versions.iter().all(|&v| v == continuing_versions[0]) {
                // All continuing branches have the same version
                let branch_v = continuing_versions[0];
                if branch_v > snapshot_v {
                    // A new versioned variable was created in all continuing branches
                    let versioned_var = format!("@mut_{var}_{branch_v}");
                    forward_decls.push(SimpleLine::ForwardDeclaration {
                        var: versioned_var.clone(),
                    });
                    // Remove forward declarations from inside the branches to avoid shadowing
                    for branch in branches.iter_mut() {
                        remove_forward_declarations(branch, &versioned_var);
                    }
                }
                self.versions.insert(var.clone(), branch_v);
            } else {
                // Versions differ among continuing branches - need to unify
                let max_version = continuing_versions.iter().copied().max().unwrap();
                let unified_version = max_version + 1;
                let unified_var = format!("@mut_{var}_{unified_version}");

                forward_decls.push(SimpleLine::ForwardDeclaration {
                    var: unified_var.clone(),
                });

                // Add equality assignment at the end of each branch that doesn't exit early
                for (branch_idx, branch_v) in versions.iter().enumerate() {
                    if branch_exits_early[branch_idx] {
                        // Skip branches that exit early - they never reach code after the if/match
                        continue;
                    }
                    let branch_var_name: Var = format!("@mut_{var}_{branch_v}");
                    branches[branch_idx].push(SimpleLine::equality(unified_var.clone(), branch_var_name));
                }

                self.versions.insert(var.clone(), unified_version);
            }
        }

        // Remove branch-local variables from tracker - they're out of scope
        for var in branch_local_vars {
            self.versions.remove(&var);
        }

        forward_decls
    }
}

/// Compile-time vector. Scalars hold variable names; Vectors hold nested values.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VectorValue {
    Scalar { var: Var },
    Vector(Vec<VectorValue>),
}

impl VectorValue {
    pub fn len(&self) -> usize {
        match self {
            Self::Vector(v) => v.len(),
            _ => panic!("len on scalar"),
        }
    }

    pub fn is_vector(&self) -> bool {
        matches!(self, Self::Vector(_))
    }

    fn get(&self, i: usize) -> Option<&Self> {
        match self {
            Self::Vector(v) => v.get(i),
            _ => None,
        }
    }

    fn get_mut(&mut self, i: usize) -> Option<&mut Self> {
        match self {
            Self::Vector(v) => v.get_mut(i),
            _ => None,
        }
    }

    pub fn navigate(&self, idx: &[usize]) -> Option<&Self> {
        idx.iter().try_fold(self, |v, &i| v.get(i))
    }

    pub fn navigate_mut(&mut self, idx: &[usize]) -> Option<&mut Self> {
        idx.iter().try_fold(self, |v, &i| v.get_mut(i))
    }

    pub fn push(&mut self, elem: Self) {
        match self {
            Self::Vector(v) => v.push(elem),
            _ => panic!("push on scalar"),
        }
    }

    pub fn pop(&mut self) -> Option<Self> {
        match self {
            Self::Vector(v) => v.pop(),
            _ => panic!("pop on scalar"),
        }
    }
}

#[derive(Debug, Clone, Default)]
struct VectorTracker {
    vectors: BTreeMap<Var, VectorValue>,
}

impl VectorTracker {
    fn register(&mut self, var: &Var, value: VectorValue) {
        self.vectors.insert(var.clone(), value);
    }

    fn is_vector(&self, var: &Var) -> bool {
        self.vectors.contains_key(var)
    }

    fn get(&self, var: &Var) -> Option<&VectorValue> {
        self.vectors.get(var)
    }

    fn get_mut(&mut self, var: &Var) -> Option<&mut VectorValue> {
        self.vectors.get_mut(var)
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

fn build_vector_value(
    ctx: &SimplifyContext<'_>,
    state: &mut SimplifyState<'_>,
    const_malloc: &mut ConstMalloc,
    elements: &[VecLiteral],
    lines: &mut Vec<SimpleLine>,
    location: SourceLocation,
) -> Result<VectorValue, String> {
    let mut vec_elements = Vec::new();

    for elem in elements {
        vec_elements.push(build_vector_value_from_element(
            ctx,
            state,
            const_malloc,
            elem,
            lines,
            location,
        )?);
    }

    Ok(VectorValue::Vector(vec_elements))
}

fn build_vector_value_from_element(
    ctx: &SimplifyContext<'_>,
    state: &mut SimplifyState<'_>,
    const_malloc: &mut ConstMalloc,
    element: &VecLiteral,
    lines: &mut Vec<SimpleLine>,
    location: SourceLocation,
) -> Result<VectorValue, String> {
    match element {
        VecLiteral::Vec(inner) => build_vector_value(ctx, state, const_malloc, inner, lines, location),
        VecLiteral::Expr(expr) => {
            // Scalar expression - create auxiliary variable and emit assignment
            let aux_var = state.counters.aux_var();
            let simplified_value = simplify_expr(ctx, state, const_malloc, expr, lines)?;
            lines.push(SimpleLine::equality(aux_var.clone(), simplified_value));
            Ok(VectorValue::Scalar { var: aux_var })
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn simplify_lines(
    ctx: &SimplifyContext<'_>,
    state: &mut SimplifyState<'_>,
    const_malloc: &mut ConstMalloc,
    new_functions: &mut BTreeMap<String, SimpleFunction>,
    n_returned_vars: usize,
    lines: &[Line],
    in_a_loop: bool,
) -> Result<Vec<SimpleLine>, String> {
    let mut res = Vec::new();
    for line in lines {
        match line {
            Line::ForwardDeclaration { var, is_mutable } => {
                if *is_mutable {
                    state.mut_tracker.register_mutable(var);
                }
                let versioned_var = if *is_mutable {
                    state.mut_tracker.current_name(var)
                } else {
                    var.clone()
                };
                res.push(SimpleLine::ForwardDeclaration { var: versioned_var });
            }
            Line::Match { value, arms, .. } => {
                // Validate patterns are consecutive
                let first_pattern = arms.first().map(|(p, _)| *p).unwrap_or(0);
                for (i, (pattern, _)) in arms.iter().enumerate() {
                    if *pattern != first_pattern + i {
                        return Err(format!(
                            "match patterns must be consecutive, expected {} but got {}",
                            first_pattern + i,
                            pattern
                        ));
                    }
                }

                let simple_value = simplify_expr(ctx, state, const_malloc, value, &mut res)?;

                // Snapshot state before processing arms
                let mut_tracker_snapshot = state.mut_tracker.clone();
                let array_manager_snapshot = state.array_manager.clone();

                let mut simple_arms = vec![];
                let mut arm_versions = vec![];

                for (_, statements) in arms.iter() {
                    // Restore snapshot for each arm
                    *state.mut_tracker = mut_tracker_snapshot.clone();
                    *state.array_manager = array_manager_snapshot.clone();

                    let arm_simplified = simplify_lines(
                        ctx,
                        state,
                        const_malloc,
                        new_functions,
                        n_returned_vars,
                        statements,
                        in_a_loop,
                    )?;
                    simple_arms.push(arm_simplified);
                    arm_versions.push(state.mut_tracker.versions.clone());
                }

                // Unify mutable variable versions across all arms
                let forward_decls = state.mut_tracker.unify_branch_versions(
                    &mut_tracker_snapshot.versions,
                    &arm_versions,
                    &mut simple_arms,
                );
                res.extend(forward_decls);

                // Restore array manager to snapshot state
                *state.array_manager = array_manager_snapshot;

                res.push(SimpleLine::Match {
                    value: simple_value,
                    arms: simple_arms,
                    offset: first_pattern,
                });
            }
            Line::Statement {
                targets,
                value,
                location,
            } => {
                // Helper function to get the target variable name, handling mutable variable versioning
                let get_target_var_name =
                    |state: &mut SimplifyState<'_>, var: &Var, is_mutable: bool| -> Result<Var, String> {
                        if is_mutable {
                            // First assignment with `mut` - register as mutable
                            state.mut_tracker.register_mutable(var);
                            // Return versioned name so subsequent reads can find it
                            Ok(state.mut_tracker.current_name(var))
                        } else if state.mut_tracker.is_mutable(var) {
                            // Increment version and get new variable name
                            Ok(state.mut_tracker.increment_version(var))
                        } else {
                            // Check for reassignment of immutable variable
                            state.mut_tracker.check_immutable_assignment(var)?;
                            Ok(var.clone())
                        }
                    };

                match value {
                    Expression::FunctionCall {
                        function_name, args, ..
                    } => {
                        // Special handling for Array builtin
                        if function_name == "Array" {
                            if args.len() != 1 {
                                return Err(format!(
                                    "Array expects exactly 1 argument, got {}, at {location}",
                                    args.len()
                                ));
                            }
                            if targets.len() != 1 {
                                return Err(format!(
                                    "Array expects exactly 1 return target, got {}, at {location}",
                                    targets.len()
                                ));
                            }
                            let target = &targets[0];
                            match target {
                                AssignmentTarget::Var { var, is_mutable } => {
                                    let target_var = get_target_var_name(state, var, *is_mutable)?;
                                    let simplified_size = simplify_expr(ctx, state, const_malloc, &args[0], &mut res)?;
                                    match simplified_size {
                                        SimpleExpr::Constant(const_size) => {
                                            let label = const_malloc.counter;
                                            const_malloc.counter += 1;
                                            const_malloc.map.insert(target_var.clone(), label);
                                            res.push(SimpleLine::ConstMalloc {
                                                var: target_var,
                                                size: const_size,
                                                label,
                                            });
                                        }
                                        _ => {
                                            res.push(SimpleLine::HintMAlloc {
                                                var: target_var,
                                                size: simplified_size,
                                            });
                                        }
                                    }
                                }
                                AssignmentTarget::ArrayAccess { .. } => {
                                    return Err(format!(
                                        "Array does not support array access as return target, at {location}"
                                    ));
                                }
                            }
                            continue;
                        }

                        // Special handling for print builtin
                        if function_name == "print" {
                            if !targets.is_empty() {
                                return Err(format!("print should not return values, at {location}"));
                            }
                            let simplified_content = args
                                .iter()
                                .map(|arg| simplify_expr(ctx, state, const_malloc, arg, &mut res))
                                .collect::<Result<Vec<_>, _>>()?;
                            res.push(SimpleLine::Print {
                                line_info: format!("line {}", location.line_number),
                                content: simplified_content,
                            });
                            continue;
                        }

                        // Special handling for precompile functions (poseidon16, dot_product)
                        if let Some(table) = ALL_TABLES.into_iter().find(|p| p.name() == function_name)
                            && !table.is_execution_table()
                        {
                            if !targets.is_empty() {
                                return Err(format!(
                                    "Precompile {function_name} should not return values, at {location}"
                                ));
                            }
                            let simplified_args = args
                                .iter()
                                .map(|arg| simplify_expr(ctx, state, const_malloc, arg, &mut res))
                                .collect::<Result<Vec<_>, _>>()?;
                            res.push(SimpleLine::Precompile {
                                table,
                                args: simplified_args,
                            });
                            continue;
                        }

                        // Special handling for custom hints
                        if let Some(hint) = CustomHint::find_by_name(function_name) {
                            if !targets.is_empty() {
                                return Err(format!(
                                    "Custom hint {function_name} should not return values, at {location}"
                                ));
                            }
                            if !hint.n_args_range().contains(&args.len()) {
                                return Err(format!(
                                    "Custom hint {function_name}: invalid number of arguments, at {location}"
                                ));
                            }
                            let simplified_args = args
                                .iter()
                                .map(|arg| simplify_expr(ctx, state, const_malloc, arg, &mut res))
                                .collect::<Result<Vec<_>, _>>()?;
                            res.push(SimpleLine::CustomHint(hint, simplified_args));
                            continue;
                        }

                        // Regular function call - may have zero, one, or multiple targets
                        let function = ctx
                            .functions
                            .get(function_name)
                            .ok_or_else(|| format!("Function used but not defined: {function_name}, at {location}"))?;
                        if targets.len() != function.n_returned_vars {
                            return Err(format!(
                                "Expected {} returned vars (and not {}) in call to {function_name}, at {location}",
                                function.n_returned_vars,
                                targets.len()
                            ));
                        }
                        if args.len() != function.arguments.len() {
                            return Err(format!(
                                "Expected {} arguments (and not {}) in call to {function_name}, at {location}",
                                function.arguments.len(),
                                args.len()
                            ));
                        }

                        let simplified_args = args
                            .iter()
                            .map(|arg| simplify_expr(ctx, state, const_malloc, arg, &mut res))
                            .collect::<Result<Vec<_>, _>>()?;

                        let mut temp_vars = Vec::new();
                        let mut array_targets: Vec<(usize, Var, Box<Expression>)> = Vec::new();

                        for (i, target) in targets.iter().enumerate() {
                            match target {
                                AssignmentTarget::Var { var, is_mutable } => {
                                    let target_var = get_target_var_name(state, var, *is_mutable)?;
                                    // Add forward declaration for new versioned variable
                                    if *is_mutable || state.mut_tracker.current_version(var) > 0 {
                                        res.push(SimpleLine::ForwardDeclaration {
                                            var: target_var.clone(),
                                        });
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
                            location: *location,
                        });

                        // For array access targets, add DEREF instructions to copy temp to array element
                        for (i, array, index) in array_targets {
                            let simplified_index = simplify_expr(ctx, state, const_malloc, &index, &mut res)?;
                            let simplified_value = VarOrConstMallocAccess::Var(temp_vars[i].clone()).into();
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
                                        )?;
                                        let target_var = get_target_var_name(state, var, *is_mutable)?;
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
                                        // Check if array is a vector (needs to be handled before simplifying indices)
                                        let versioned_array = state.mut_tracker.current_name(array);
                                        if state.vec_tracker.is_vector(&versioned_array) {
                                            // Use simplify_expr which handles vectors correctly
                                            let simplified_val = simplify_expr(
                                                ctx,
                                                state,
                                                const_malloc,
                                                &Expression::ArrayAccess {
                                                    array: array.clone(),
                                                    index: index.clone(),
                                                },
                                                &mut res,
                                            )?;
                                            let target_var = get_target_var_name(state, var, *is_mutable)?;
                                            res.push(SimpleLine::equality(target_var, simplified_val));
                                        } else {
                                            // Pre-simplify indices before version update
                                            let simplified_index = index
                                                .iter()
                                                .map(|idx| simplify_expr(ctx, state, const_malloc, idx, &mut res))
                                                .collect::<Result<Vec<_>, _>>()?;
                                            let target_var = get_target_var_name(state, var, *is_mutable)?;
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
                                    }
                                    Expression::MathExpr(operation, args) => {
                                        let args_simplified = args
                                            .iter()
                                            .map(|arg| simplify_expr(ctx, state, const_malloc, arg, &mut res))
                                            .collect::<Result<Vec<_>, _>>()?;
                                        let target_var = get_target_var_name(state, var, *is_mutable)?;
                                        if state.mut_tracker.is_mutable(var)
                                            && state.mut_tracker.current_version(var) > 0
                                        {
                                            res.push(SimpleLine::ForwardDeclaration {
                                                var: target_var.clone(),
                                            });
                                        }
                                        // If all operands are constants, evaluate at compile time
                                        if let Some(const_args) = SimpleExpr::try_vec_as_constant(&args_simplified) {
                                            let result = ConstExpression::MathExpr(*operation, const_args);
                                            res.push(SimpleLine::equality(target_var, SimpleExpr::Constant(result)));
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
                                    Expression::Lambda { .. } => {
                                        unreachable!("Lambda should be expanded by match_range")
                                    }
                                }
                            }
                            AssignmentTarget::ArrayAccess { array, index } => {
                                // Array element assignment - pre-simplify index first
                                let simplified_index = simplify_expr(ctx, state, const_malloc, index, &mut res)?;

                                // Optimization: direct math assignment to const_malloc array with constant index
                                if let SimpleExpr::Constant(offset) = &simplified_index
                                    && let Some(label) = const_malloc.map.get(array)
                                    && let Expression::MathExpr(operation, args) = value
                                {
                                    let var = VarOrConstMallocAccess::ConstMallocAccess {
                                        malloc_label: *label,
                                        offset: offset.clone(),
                                    };
                                    let simplified_args = args
                                        .iter()
                                        .map(|arg| simplify_expr(ctx, state, const_malloc, arg, &mut res))
                                        .collect::<Result<Vec<_>, _>>()?;
                                    // If all operands are constants, evaluate at compile time
                                    if let Some(const_args) = SimpleExpr::try_vec_as_constant(&simplified_args) {
                                        let result = ConstExpression::MathExpr(*operation, const_args);
                                        res.push(SimpleLine::equality(var, SimpleExpr::Constant(result)));
                                    } else {
                                        assert_eq!(simplified_args.len(), 2);
                                        res.push(SimpleLine::Assignment {
                                            var,
                                            operation: *operation,
                                            arg0: simplified_args[0].clone(),
                                            arg1: simplified_args[1].clone(),
                                        });
                                    }
                                } else {
                                    // General case: pre-simplify value and use handle_array_assignment
                                    let simplified_value = simplify_expr(ctx, state, const_malloc, value, &mut res)?;
                                    handle_array_assignment(
                                        ctx,
                                        state,
                                        &mut res,
                                        array,
                                        &[simplified_index],
                                        ArrayAccessType::ArrayIsAssigned(simplified_value),
                                    );
                                }
                            }
                        }
                    }
                }
            }
            Line::Assert {
                boolean,
                debug,
                location,
            } => {
                let left = simplify_expr(ctx, state, const_malloc, &boolean.left, &mut res)?;
                let right = simplify_expr(ctx, state, const_malloc, &boolean.right, &mut res)?;
                if *debug {
                    res.push(SimpleLine::DebugAssert(
                        BooleanExpr {
                            left,
                            right,
                            kind: boolean.kind,
                        },
                        *location,
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
                                else_branch: vec![SimpleLine::Panic { message: None }],
                                location: *location,
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
                                        return Err(format!(
                                            "Compile-time assertion failed: {} != {} ({})",
                                            left_val.to_usize(),
                                            right_val.to_usize(),
                                            location
                                        ));
                                    }
                                }
                                return Err(format!("Unsupported equality assertion: {left:?}, {right:?}"));
                            };
                            res.push(SimpleLine::equality(var, other));
                        }
                        Boolean::LessThan => {
                            // assert left < right is equivalent to assert left <= right - 1
                            let bound_minus_one = state.counters.aux_var();
                            res.push(SimpleLine::Assignment {
                                var: bound_minus_one.clone().into(),
                                operation: MathOperation::Sub,
                                arg0: right,
                                arg1: SimpleExpr::one(),
                            });

                            // We add a debug assert for sanity
                            res.push(SimpleLine::DebugAssert(
                                BooleanExpr {
                                    kind: Boolean::LessOrEqual,
                                    left: left.clone(),
                                    right: bound_minus_one.clone().into(),
                                },
                                *location,
                            ));

                            res.push(SimpleLine::RangeCheck {
                                val: left,
                                bound: bound_minus_one.into(),
                            });
                        }
                        Boolean::LessOrEqual => {
                            // Range check: assert left <= right

                            // we add a debug assert for sanity
                            res.push(SimpleLine::DebugAssert(
                                BooleanExpr {
                                    kind: Boolean::LessOrEqual,
                                    left: left.clone(),
                                    right: right.clone(),
                                },
                                *location,
                            ));

                            res.push(SimpleLine::RangeCheck {
                                val: left,
                                bound: right,
                            });
                        }
                    }
                }
            }
            Line::IfCondition {
                condition,
                then_branch,
                else_branch,
                location,
            } => {
                let (condition_simplified, then_branch, else_branch) = match condition {
                    Condition::Comparison(condition) => {
                        // Transform if a == b then X else Y into if a != b then Y else X

                        let (left, right, then_branch, else_branch) = match condition.kind {
                            Boolean::Equal => (&condition.left, &condition.right, else_branch, then_branch), // switched
                            Boolean::Different => (&condition.left, &condition.right, then_branch, else_branch),
                            Boolean::LessThan | Boolean::LessOrEqual => unreachable!(),
                        };

                        let left_simplified = simplify_expr(ctx, state, const_malloc, left, &mut res)?;
                        let right_simplified = simplify_expr(ctx, state, const_malloc, right, &mut res)?;

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
                        let condition_simplified = simplify_expr(ctx, state, const_malloc, condition, &mut res)?;

                        (condition_simplified, then_branch, else_branch)
                    }
                };

                // Snapshot state before processing branches
                let mut_tracker_snapshot = state.mut_tracker.clone();
                let vec_tracker_snapshot = state.vec_tracker.clone();

                let mut array_manager_then = state.array_manager.clone();
                let mut mut_tracker_then = state.mut_tracker.clone();
                let mut vec_tracker_then = state.vec_tracker.clone();
                let mut state_then = SimplifyState {
                    counters: state.counters,
                    array_manager: &mut array_manager_then,
                    mut_tracker: &mut mut_tracker_then,
                    vec_tracker: &mut vec_tracker_then,
                };
                let then_branch_simplified = simplify_lines(
                    ctx,
                    &mut state_then,
                    const_malloc,
                    new_functions,
                    n_returned_vars,
                    then_branch,
                    in_a_loop,
                )?;
                let then_versions = mut_tracker_then.versions.clone();

                let mut array_manager_else = array_manager_then.clone();
                array_manager_else.valid = state.array_manager.valid.clone(); // Crucial: remove the access added in the IF branch

                // Restore state for else branch
                let mut mut_tracker_else = mut_tracker_snapshot.clone();
                let mut vec_tracker_else = vec_tracker_snapshot.clone();

                let mut state_else = SimplifyState {
                    counters: state.counters,
                    array_manager: &mut array_manager_else,
                    mut_tracker: &mut mut_tracker_else,
                    vec_tracker: &mut vec_tracker_else,
                };
                let else_branch_simplified = simplify_lines(
                    ctx,
                    &mut state_else,
                    const_malloc,
                    new_functions,
                    n_returned_vars,
                    else_branch,
                    in_a_loop,
                )?;
                let else_versions = mut_tracker_else.versions.clone();

                // Unify mutable variable versions across both branches
                let branch_versions = vec![then_versions, else_versions];
                let mut branches = vec![then_branch_simplified, else_branch_simplified];
                let forward_decls = state.mut_tracker.unify_branch_versions(
                    &mut_tracker_snapshot.versions,
                    &branch_versions,
                    &mut branches,
                );
                res.extend(forward_decls);
                let [then_branch_simplified, else_branch_simplified] = <[_; 2]>::try_from(branches).unwrap();

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
                    location: *location,
                });
            }
            Line::ForLoop {
                iterator,
                start,
                end,
                body,
                unroll,
                location,
            } => {
                assert!(!*unroll, "Unrolled loops should have been handled already");

                let mut loop_const_malloc = ConstMalloc {
                    counter: const_malloc.counter,
                    ..ConstMalloc::default()
                };
                let valid_aux_vars_in_array_manager_before = state.array_manager.valid.clone();
                state.array_manager.valid.clear();

                // Loop body becomes a separate function, so immutable assignments inside
                // shouldn't affect outer scope (but mutable variable versions persist)
                let assigned_before = std::mem::take(&mut state.mut_tracker.assigned);
                let simplified_body = simplify_lines(ctx, state, &mut loop_const_malloc, new_functions, 0, body, true)?;
                state.mut_tracker.assigned = assigned_before;

                const_malloc.counter = loop_const_malloc.counter;
                state.array_manager.valid = valid_aux_vars_in_array_manager_before; // restore the valid aux vars

                let func_name = format!("@loop_{}_{}", state.counters.loops.get_next(), location);

                // Find variables used inside loop but defined outside
                let (_, mut external_vars) = find_variable_usage(body, ctx.const_arrays);

                // Include variables in start/end
                for expr in [start, end] {
                    for var in vars_in_expression(expr, ctx.const_arrays) {
                        external_vars.insert(var);
                    }
                }
                external_vars.remove(iterator); // Iterator is internal to loop

                let mut external_vars: Vec<_> = external_vars
                    .into_iter()
                    .map(|var| state.mut_tracker.current_name(&var))
                    .collect();

                let start_simplified = simplify_expr(ctx, state, const_malloc, start, &mut res)?;
                let mut end_simplified = simplify_expr(ctx, state, const_malloc, end, &mut res)?;
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
                    *location,
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
                    location: *location,
                });
            }
            Line::FunctionRet { return_data } => {
                if in_a_loop {
                    return Err("Function return inside a loop is not currently supported".to_string());
                }
                if return_data.len() != n_returned_vars {
                    return Err(format!(
                        "Wrong number of return values in return statement; expected {n_returned_vars} but got {}",
                        return_data.len()
                    ));
                }
                let simplified_return_data = return_data
                    .iter()
                    .map(|ret| simplify_expr(ctx, state, const_malloc, ret, &mut res))
                    .collect::<Result<Vec<_>, _>>()?;
                res.push(SimpleLine::FunctionRet {
                    return_data: simplified_return_data,
                });
            }
            Line::Panic { message } => {
                res.push(SimpleLine::Panic {
                    message: message.clone(),
                });
            }
            Line::LocationReport { location } => {
                res.push(SimpleLine::LocationReport { location: *location });
            }
            Line::VecDeclaration {
                var,
                elements,
                location,
            } => {
                let vector_value = build_vector_value(ctx, state, const_malloc, elements, &mut res, *location)?;
                state.vec_tracker.register(var, vector_value);
                // No SimpleLine for the variable itself - vector metadata is compile-time only
            }
            Line::Push {
                vector,
                indices,
                element,
                location,
            } => {
                // Get the vector and check it's a tracked vector
                if !state.vec_tracker.is_vector(vector) {
                    return Err(format!(
                        "push called on non-vector variable '{}', at {}",
                        vector, location
                    ));
                }

                // Evaluate indices at compile time
                let const_indices: Vec<usize> = indices
                    .iter()
                    .map(|idx| {
                        let simplified = simplify_expr(ctx, state, const_malloc, idx, &mut res)?;
                        let const_val = simplified
                            .as_constant()
                            .ok_or_else(|| format!("push index must be a compile-time constant, at {}", location))?;
                        let val = const_val
                            .naive_eval()
                            .ok_or_else(|| format!("push index must be evaluable at compile time, at {}", location))?;
                        Ok(val.to_usize())
                    })
                    .collect::<Result<Vec<_>, String>>()?;

                // Build VectorValue for the element being pushed
                let new_element =
                    build_vector_value_from_element(ctx, state, const_malloc, element, &mut res, *location)?;

                // Navigate to the target vector and push
                let vector_value = state
                    .vec_tracker
                    .get_mut(vector)
                    .expect("Vector should exist after is_vector check");

                if const_indices.is_empty() {
                    // Push directly to the top-level vector
                    vector_value.push(new_element);
                } else {
                    // Navigate to the nested vector and push
                    let target = vector_value
                        .navigate_mut(&const_indices)
                        .ok_or_else(|| format!("push target index out of bounds, at {}", location))?;
                    if !target.is_vector() {
                        return Err(format!("push target must be a vector, not a scalar, at {}", location));
                    }
                    target.push(new_element);
                }
            }
            Line::Pop {
                vector,
                indices,
                location,
            } => {
                // Get the vector and check it's a tracked vector
                if !state.vec_tracker.is_vector(vector) {
                    return Err(format!(
                        "pop called on non-vector variable '{}', at {}",
                        vector, location
                    ));
                }

                // Evaluate indices at compile time
                let const_indices: Vec<usize> = indices
                    .iter()
                    .map(|idx| {
                        let simplified = simplify_expr(ctx, state, const_malloc, idx, &mut res)?;
                        let const_val = simplified
                            .as_constant()
                            .ok_or_else(|| format!("pop index must be a compile-time constant, at {}", location))?;
                        let val = const_val
                            .naive_eval()
                            .ok_or_else(|| format!("pop index must be evaluable at compile time, at {}", location))?;
                        Ok(val.to_usize())
                    })
                    .collect::<Result<Vec<_>, String>>()?;

                // Navigate to the target vector and pop
                let vector_value = state
                    .vec_tracker
                    .get_mut(vector)
                    .expect("Vector should exist after is_vector check");

                if const_indices.is_empty() {
                    // Pop directly from the top-level vector
                    if vector_value.len() == 0 {
                        return Err(format!("pop on empty vector '{}', at {}", vector, location));
                    }
                    vector_value.pop();
                } else {
                    // Navigate to the nested vector and pop
                    let target = vector_value
                        .navigate_mut(&const_indices)
                        .ok_or_else(|| format!("pop target index out of bounds, at {}", location))?;
                    if !target.is_vector() {
                        return Err(format!("pop target must be a vector, not a scalar, at {}", location));
                    }
                    if target.len() == 0 {
                        return Err(format!("pop on empty vector, at {}", location));
                    }
                    target.pop();
                }
            }
        }
    }

    Ok(res)
}

fn simplify_expr(
    ctx: &SimplifyContext<'_>,
    state: &mut SimplifyState<'_>,
    const_malloc: &ConstMalloc,
    expr: &Expression,
    lines: &mut Vec<SimpleLine>,
) -> Result<SimpleExpr, String> {
    match expr {
        Expression::Value(value) => {
            // Translate mutable variable references to their current versioned name
            if let SimpleExpr::Memory(VarOrConstMallocAccess::Var(var)) = value {
                let versioned_var = state.mut_tracker.current_name(var);
                Ok(versioned_var.into())
            } else {
                Ok(value.clone())
            }
        }
        Expression::ArrayAccess { array, index } => {
            // Check for const array access
            if let Some(arr) = ctx.const_arrays.get(array) {
                let simplified_index = index
                    .iter()
                    .map(|idx| {
                        idx.as_scalar()
                            .ok_or_else(|| "Const array access index must be a compile-time constant".to_string())
                    })
                    .collect::<Result<Vec<_>, String>>()?;

                return Ok(SimpleExpr::Constant(ConstExpression::scalar(
                    arr.navigate(&simplified_index)
                        .unwrap_or_else(|| panic!("Const array index out of bounds for array '{}'", array))
                        .as_scalar()
                        .expect("Const array access should return a scalar"),
                )));
            }

            // Check for compile-time vector access
            let versioned_array = state.mut_tracker.current_name(array);
            if state.vec_tracker.is_vector(&versioned_array) {
                // Vector access - indices must all be compile-time constant
                // First, simplify all indices (this may mutate state)
                let mut const_indices: Vec<usize> = Vec::new();
                for idx in index {
                    let simplified = simplify_expr(ctx, state, const_malloc, idx, lines)?;
                    let SimpleExpr::Constant(const_expr) = simplified else {
                        return Err("Vector index must be compile-time constant".to_string());
                    };
                    let val = const_expr
                        .naive_eval()
                        .ok_or_else(|| "Cannot evaluate vector index".to_string())?
                        .to_usize();
                    const_indices.push(val);
                }

                // Now we can borrow vec_tracker again
                let vector_value = state.vec_tracker.get(&versioned_array).unwrap();

                // Navigate to the element
                let element = vector_value
                    .navigate(&const_indices)
                    .ok_or_else(|| format!("Vector index out of bounds: {:?}", const_indices))?;

                match element {
                    VectorValue::Scalar { var } => {
                        // Return memory reference to this variable
                        return Ok(SimpleExpr::Memory(VarOrConstMallocAccess::Var(var.clone())));
                    }
                    VectorValue::Vector(_) => {
                        return Err("Cannot use nested vector as expression value".to_string());
                    }
                }
            }

            assert_eq!(index.len(), 1);
            let index = index[0].clone();

            if let Some(label) = const_malloc.map.get(array)
                && let Ok(offset) = ConstExpression::try_from(index.clone())
            {
                return Ok(VarOrConstMallocAccess::ConstMallocAccess {
                    malloc_label: *label,
                    offset,
                }
                .into());
            }

            let versioned_array = state.mut_tracker.current_name(array);
            let aux_arr = state.array_manager.get_aux_var(&versioned_array, &index); // auxiliary var to store m[array + index]

            if !state.array_manager.valid.insert(aux_arr.clone()) {
                return Ok(VarOrConstMallocAccess::Var(aux_arr).into());
            }

            let simplified_index = simplify_expr(ctx, state, const_malloc, &index, lines)?;
            handle_array_assignment(
                ctx,
                state,
                lines,
                array,
                &[simplified_index],
                ArrayAccessType::VarIsAssigned(aux_arr.clone()),
            );
            Ok(VarOrConstMallocAccess::Var(aux_arr).into())
        }
        Expression::MathExpr(operation, args) => {
            let simplified_args = args
                .iter()
                .map(|arg| simplify_expr(ctx, state, const_malloc, arg, lines))
                .collect::<Result<Vec<_>, _>>()?;
            if let Some(const_args) = SimpleExpr::try_vec_as_constant(&simplified_args) {
                return Ok(SimpleExpr::Constant(ConstExpression::MathExpr(*operation, const_args)));
            }
            let aux_var = state.counters.aux_var();
            assert_eq!(simplified_args.len(), 2);
            lines.push(SimpleLine::Assignment {
                var: aux_var.clone().into(),
                operation: *operation,
                arg0: simplified_args[0].clone(),
                arg1: simplified_args[1].clone(),
            });
            Ok(VarOrConstMallocAccess::Var(aux_var).into())
        }
        Expression::FunctionCall {
            function_name,
            args,
            location,
        } => {
            let function = ctx
                .functions
                .get(function_name)
                .unwrap_or_else(|| panic!("Function used but not defined: {function_name}"));
            if function.n_returned_vars != 1 {
                return Err(format!(
                    "Nested function calls must return exactly one value (function {function_name} returns {} values)",
                    function.n_returned_vars
                ));
            }

            let simplified_args = args
                .iter()
                .map(|arg| simplify_expr(ctx, state, const_malloc, arg, lines))
                .collect::<Result<Vec<_>, _>>()?;

            // Create a temporary variable for the function result
            let result_var = state.counters.aux_var();

            lines.push(SimpleLine::FunctionCall {
                function_name: function_name.clone(),
                args: simplified_args,
                return_data: vec![result_var.clone()],
                location: *location,
            });

            Ok(VarOrConstMallocAccess::Var(result_var).into())
        }
        Expression::Len { array, indices } => {
            // Check for compile-time vector len()
            let versioned_array = state.mut_tracker.current_name(array);
            if state.vec_tracker.is_vector(&versioned_array) {
                // Evaluate indices at compile time - first simplify to avoid borrow issues
                let mut const_indices: Vec<usize> = Vec::new();
                for idx in indices {
                    let simplified = simplify_expr(ctx, state, const_malloc, idx, lines)?;
                    let SimpleExpr::Constant(const_expr) = simplified else {
                        return Err("Vector len() index must be compile-time constant".to_string());
                    };
                    let val = const_expr
                        .naive_eval()
                        .ok_or_else(|| "Cannot evaluate len() index".to_string())?
                        .to_usize();
                    const_indices.push(val);
                }

                // Now we can borrow vec_tracker again
                let vector_value = state.vec_tracker.get(&versioned_array).unwrap();

                // Navigate and get length
                let target = if const_indices.is_empty() {
                    vector_value
                } else {
                    vector_value
                        .navigate(&const_indices)
                        .ok_or_else(|| "len() index out of bounds".to_string())?
                };

                return Ok(SimpleExpr::Constant(ConstExpression::from(target.len())));
            }

            // Fall through to const array handling (should be unreachable for vectors)
            unreachable!("len() should have been resolved at parse time for const arrays")
        }
        Expression::Lambda { .. } => Err("Lambda expressions can only be used as arguments to match_range".to_string()),
    }
}

fn remove_forward_declarations(lines: &mut Vec<SimpleLine>, var: &Var) {
    for i in (0..lines.len()).rev() {
        if let SimpleLine::ForwardDeclaration { var: decl_var } = &lines[i]
            && decl_var == var
        {
            lines.remove(i);
        } else {
            for block in lines[i].nested_blocks_mut() {
                remove_forward_declarations(block, var);
            }
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
            Condition::AssumeBoolean(expr) => {
                on_new_expr(expr, internal_vars, external_vars);
            }
        };

    for line in lines {
        match line {
            Line::ForwardDeclaration { var, .. } => {
                internal_vars.insert(var.clone());
            }
            Line::Match { value, arms, .. } => {
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
                ..
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
            Line::ForLoop {
                iterator,
                start,
                end,
                body,
                ..
            } => {
                let (body_internal, body_external) = find_variable_usage(body, const_arrays);
                internal_vars.extend(body_internal);
                internal_vars.insert(iterator.clone());
                external_vars.extend(body_external.difference(&internal_vars).cloned());
                on_new_expr(start, &internal_vars, &mut external_vars);
                on_new_expr(end, &internal_vars, &mut external_vars);
            }
            Line::Panic { .. } | Line::LocationReport { .. } => {}
            Line::VecDeclaration { var, elements, .. } => {
                // Process expressions in vec elements
                process_vec_elements_usage(elements, &internal_vars, &mut external_vars, const_arrays);
                // Add the vector variable to internal vars
                internal_vars.insert(var.clone());
            }
            Line::Push {
                vector,
                indices,
                element,
                ..
            } => {
                // The vector variable is used
                if !internal_vars.contains(vector) {
                    external_vars.insert(vector.clone());
                }
                // Process index expressions
                for idx in indices {
                    on_new_expr(idx, &internal_vars, &mut external_vars);
                }
                // Process the pushed element
                process_vec_element_usage(element, &internal_vars, &mut external_vars, const_arrays);
            }
            Line::Pop { vector, indices, .. } => {
                // The vector variable is used
                if !internal_vars.contains(vector) {
                    external_vars.insert(vector.clone());
                }
                // Process index expressions
                for idx in indices {
                    on_new_expr(idx, &internal_vars, &mut external_vars);
                }
            }
        }
    }

    (internal_vars, external_vars)
}

fn process_vec_elements_usage(
    elements: &[VecLiteral],
    internal_vars: &BTreeSet<Var>,
    external_vars: &mut BTreeSet<Var>,
    const_arrays: &BTreeMap<String, ConstArrayValue>,
) {
    for elem in elements {
        process_vec_element_usage(elem, internal_vars, external_vars, const_arrays);
    }
}

fn process_vec_element_usage(
    elem: &VecLiteral,
    internal_vars: &BTreeSet<Var>,
    external_vars: &mut BTreeSet<Var>,
    const_arrays: &BTreeMap<String, ConstArrayValue>,
) {
    match elem {
        VecLiteral::Expr(expr) => {
            for var in vars_in_expression(expr, const_arrays) {
                if !internal_vars.contains(&var) && !const_arrays.contains_key(&var) {
                    external_vars.insert(var);
                }
            }
        }
        VecLiteral::Vec(inner) => {
            process_vec_elements_usage(inner, internal_vars, external_vars, const_arrays);
        }
    }
}

enum VarTransform {
    ReplaceWithExpr(SimpleExpr),
    Rename(String),
    Keep,
}

impl VarTransform {
    fn apply_to_var(self, var: &mut Var) {
        match self {
            VarTransform::ReplaceWithExpr(SimpleExpr::Memory(VarOrConstMallocAccess::Var(new_var))) => {
                *var = new_var;
            }
            VarTransform::ReplaceWithExpr(_) => {
                panic!("Cannot replace variable with non-variable expression in this context");
            }
            VarTransform::Rename(new_name) => {
                *var = new_name;
            }
            VarTransform::Keep => {}
        }
    }
}

fn transform_vars_in_simple_expr(simple_expr: &mut SimpleExpr, transform: &impl Fn(&Var) -> VarTransform) {
    if let SimpleExpr::Memory(VarOrConstMallocAccess::Var(var)) = simple_expr {
        match transform(var) {
            VarTransform::ReplaceWithExpr(replacement) => {
                *simple_expr = replacement;
            }
            VarTransform::Rename(new_name) => {
                *var = new_name;
            }
            VarTransform::Keep => {}
        }
    }
}

fn transform_vars_in_expr(expr: &mut Expression, transform: &impl Fn(&Var) -> VarTransform) {
    match expr {
        Expression::Value(value) => {
            transform_vars_in_simple_expr(value, transform);
        }
        Expression::ArrayAccess { array, .. } | Expression::Len { array, .. } => {
            transform(array).apply_to_var(array);
        }
        Expression::MathExpr(_, _) | Expression::FunctionCall { .. } => {}
        Expression::Lambda { param, .. } => {
            transform(param).apply_to_var(param);
        }
    }
    for inner_expr in expr.inner_exprs_mut() {
        transform_vars_in_expr(inner_expr, transform);
    }
}

fn transform_vars_in_lines(lines: &mut [Line], transform: &impl Fn(&Var) -> VarTransform) {
    for line in lines {
        for expr in line.expressions_mut() {
            transform_vars_in_expr(expr, transform);
        }
        for block in line.nested_blocks_mut() {
            transform_vars_in_lines(block, transform);
        }
        match line {
            Line::ForwardDeclaration { var, .. } => {
                transform(var).apply_to_var(var);
            }
            Line::Statement { targets, .. } => {
                for target in targets {
                    match target {
                        AssignmentTarget::Var { var, .. } => {
                            transform(var).apply_to_var(var);
                        }
                        AssignmentTarget::ArrayAccess { array, .. } => {
                            transform(array).apply_to_var(array);
                        }
                    }
                }
            }
            Line::ForLoop { iterator, .. } => {
                transform(iterator).apply_to_var(iterator);
            }
            Line::VecDeclaration { var, .. } => {
                transform(var).apply_to_var(var);
            }
            Line::Push { vector, .. } => {
                transform(vector).apply_to_var(vector);
            }
            Line::Pop { vector, .. } => {
                transform(vector).apply_to_var(vector);
            }
            _ => {}
        }
    }
}

fn inline_lines(
    lines: &mut Vec<Line>,
    args: &BTreeMap<Var, SimpleExpr>,
    const_arrays: &BTreeMap<String, ConstArrayValue>,
    res: &[AssignmentTarget],
    inlining_count: usize,
) {
    let transform = |var: &Var| -> VarTransform {
        if let Some(replacement) = args.get(var) {
            VarTransform::ReplaceWithExpr(replacement.clone())
        } else if const_arrays.contains_key(var) {
            VarTransform::Keep
        } else {
            VarTransform::Rename(format!("@inlined_var_{inlining_count}_{var}"))
        }
    };

    transform_vars_in_lines(lines, &transform);
    replace_function_ret_in_lines(lines, res);
}

fn replace_function_ret_in_lines(lines: &mut Vec<Line>, res: &[AssignmentTarget]) {
    // First recurse into nested blocks
    for line in lines.iter_mut() {
        for block in line.nested_blocks_mut() {
            replace_function_ret_in_lines(block, res);
        }
    }

    // Then handle FunctionRet → Statement conversion at this level
    let mut lines_to_replace = vec![];
    for (i, line) in lines.iter().enumerate() {
        if let Line::FunctionRet { return_data } = line {
            assert_eq!(return_data.len(), res.len());
            lines_to_replace.push((
                i,
                res.iter()
                    .zip(return_data.iter())
                    .map(|(target, expr)| Line::Statement {
                        targets: vec![target.clone()],
                        value: expr.clone(),
                        location: SourceLocation {
                            file_id: 0,
                            line_number: 0,
                        }, // TODO
                    })
                    .collect::<Vec<_>>(),
            ));
        }
    }
    for (i, new_lines) in lines_to_replace.into_iter().rev() {
        lines.splice(i..=i, new_lines);
    }
}

fn vars_in_expression(expr: &Expression, const_arrays: &BTreeMap<String, ConstArrayValue>) -> BTreeSet<Var> {
    let mut vars = BTreeSet::new();
    match expr {
        Expression::Value(SimpleExpr::Memory(VarOrConstMallocAccess::Var(var))) => {
            vars.insert(var.clone());
        }
        Expression::ArrayAccess { array, .. } if !const_arrays.contains_key(array) => {
            vars.insert(array.clone());
        }
        _ => {}
    }
    for inner_expr in expr.inner_exprs() {
        vars.extend(vars_in_expression(inner_expr, const_arrays));
    }
    vars
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ArrayAccessType {
    VarIsAssigned(Var),          // var = array[index]
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
    // Convert array name to versioned name if it's a mutable variable
    let array = state.mut_tracker.current_name(array);

    if let ArrayAccessType::VarIsAssigned(var) = &access_type
        && let Some(const_array) = ctx.const_arrays.get(&array)
    {
        let idx = simplified_index
            .iter()
            .map(|idx| {
                idx.as_constant()
                    .expect("Const array access index should be constant")
                    .naive_eval()
                    .unwrap()
            })
            .collect::<Vec<_>>();
        let value = const_array
            .navigate(&idx)
            .expect("Const array access index out of bounds")
            .as_scalar()
            .expect("Const array access should return a scalar");
        res.push(SimpleLine::equality(var.clone(), ConstExpression::scalar(value)));
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
        location,
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
            location,
        },
    ];

    SimpleFunction {
        name,
        arguments: args,
        n_returned_vars: 0,
        instructions,
    }
}

fn replace_vars_for_unroll(
    lines: &mut [Line],
    iterator: &Var,
    unroll_index: usize,
    iterator_value: usize,
    internal_vars: &BTreeSet<Var>,
) {
    let transform = |var: &Var| -> VarTransform {
        if var == iterator {
            VarTransform::ReplaceWithExpr(SimpleExpr::Constant(ConstExpression::from(iterator_value)))
        } else if internal_vars.contains(var) {
            VarTransform::Rename(format!("@unrolled_{unroll_index}_{iterator_value}_{var}"))
        } else {
            VarTransform::Keep
        }
    };

    transform_vars_in_lines(lines, &transform);
}

fn replace_vars_by_const_in_expr(expr: &mut Expression, map: &BTreeMap<Var, F>) {
    match expr {
        Expression::Value(value) => match &value {
            SimpleExpr::Memory(VarOrConstMallocAccess::Var(var)) => {
                if let Some(const_value) = map.get(var) {
                    *value = SimpleExpr::scalar(*const_value);
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
        Expression::Lambda { body, .. } => {
            replace_vars_by_const_in_expr(body, map);
        }
    }
}

fn replace_vars_by_const_in_lines(lines: &mut [Line], map: &BTreeMap<Var, F>) {
    for line in lines {
        match line {
            Line::Match { value, arms, .. } => {
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
                ..
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
            Line::LocationReport { .. } | Line::Panic { .. } => {}
            Line::VecDeclaration { .. } | Line::Push { .. } | Line::Pop { .. } => {
                // VecDeclaration, Push and Pop contain VecLiteral elements which may have expressions
                // but these are compile-time constructs handled separately
            }
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
            Self::Match { value, arms, offset } => {
                let arms_str = arms
                    .iter()
                    .enumerate()
                    .map(|(index, body)| {
                        let body = body
                            .iter()
                            .map(|line| line.to_string_with_indent(indent + 2))
                            .collect::<Vec<_>>()
                            .join("\n");

                        format!(
                            "{}{} => {{{}\n{}}}",
                            "    ".repeat(indent + 1),
                            index + offset,
                            body,
                            "    ".repeat(indent + 1),
                        )
                    })
                    .collect::<Vec<_>>()
                    .join("\n");

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
                ..
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
                ..
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
                format!("{var} = Array({size})")
            }
            Self::ConstMalloc { var, size, label: _ } => {
                format!("{var} = Array({size})")
            }
            Self::Panic { message } => match message {
                Some(msg) => format!("assert False, \"{msg}\""),
                None => "assert False".to_string(),
            },
            Self::LocationReport { .. } => Default::default(),
            Self::DebugAssert(bool, _) => {
                format!("debug_assert({bool})")
            }
            Self::RangeCheck { val, bound } => {
                format!("range_check({val} <= {bound})")
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
            write!(f, "def {}({}) -> {} {{}}", self.name, args_str, self.n_returned_vars)
        } else {
            write!(
                f,
                "def {}({}) -> {} {{\n{}\n}}",
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
