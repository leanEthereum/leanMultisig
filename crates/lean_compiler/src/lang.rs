use backend::*;
use lean_vm::*;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{Display, Formatter};
use utils::ToUsize;

use crate::a_simplify_lang::{VarOrConstMallocAccess, VectorLenTracker};
use crate::{F, parser::ConstArrayValue};
pub use lean_vm::{FileId, FunctionName, SourceLocation};

#[derive(Debug, Clone)]
pub struct Program {
    pub functions: BTreeMap<FunctionName, Function>,
    pub const_arrays: BTreeMap<String, ConstArrayValue>,
    pub function_locations: BTreeMap<SourceLocation, FunctionName>,
    pub source_code: BTreeMap<FileId, String>,
    pub filepaths: BTreeMap<FileId, String>,
}

impl Program {
    pub fn inlined_function_names(&self) -> BTreeSet<FunctionName> {
        self.functions
            .iter()
            .filter(|(_, func)| func.inlined)
            .map(|(name, _)| name.clone())
            .collect()
    }

    pub fn non_constant_functions_mut(&mut self) -> BTreeSet<&mut Function> {
        self.functions
            .iter_mut()
            .filter(|(_, func)| !func.has_const_arguments())
            .map(|(_, func)| func)
            .collect()
    }
}

/// A function argument with its modifiers
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct FunctionArg {
    pub name: Var,
    pub is_const: bool,
    pub is_mutable: bool,
}

impl FunctionArg {
    pub fn new(name: Var, is_const: bool, is_mutable: bool) -> Self {
        Self {
            name,
            is_const,
            is_mutable,
        }
    }

    pub fn simple(name: Var) -> Self {
        Self {
            name,
            is_const: false,
            is_mutable: false,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Function {
    pub name: String,
    pub arguments: Vec<FunctionArg>,
    pub inlined: bool,
    pub n_returned_vars: usize,
    pub body: Vec<Line>,
}

impl Function {
    pub fn has_const_arguments(&self) -> bool {
        self.arguments.iter().any(|arg| arg.is_const)
    }
    pub fn has_mutable_arguments(&self) -> bool {
        self.arguments.iter().any(|arg| arg.is_mutable)
    }
}

pub type Var = String;
pub type ConstMallocLabel = usize;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SimpleExpr {
    Memory(VarOrConstMallocAccess),
    Constant(ConstExpression),
}

impl SimpleExpr {
    pub fn zero() -> Self {
        Self::scalar(F::ZERO)
    }

    pub fn one() -> Self {
        Self::scalar(F::ONE)
    }

    pub fn scalar(scalar: F) -> Self {
        Self::Constant(ConstantValue::Scalar(scalar).into())
    }

    pub const fn is_constant(&self) -> bool {
        matches!(self, Self::Constant(_))
    }
}

impl From<ConstantValue> for SimpleExpr {
    fn from(constant: ConstantValue) -> Self {
        Self::Constant(constant.into())
    }
}

impl From<ConstExpression> for SimpleExpr {
    fn from(constant: ConstExpression) -> Self {
        Self::Constant(constant)
    }
}

impl From<Var> for SimpleExpr {
    fn from(var: Var) -> Self {
        VarOrConstMallocAccess::Var(var).into()
    }
}

impl SimpleExpr {
    pub fn as_constant(&self) -> Option<ConstExpression> {
        match self {
            Self::Constant(constant) => Some(constant.clone()),
            Self::Memory(_) => None,
        }
    }

    pub fn try_vec_as_constant(vec: &[Self]) -> Option<Vec<ConstExpression>> {
        let mut const_elems = Vec::new();
        for expr in vec {
            if let Self::Constant(cst) = expr {
                const_elems.push(cst.clone());
            } else {
                return None;
            }
        }
        Some(const_elems)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ConstantValue {
    Scalar(F),
    FunctionSize { function_name: Label },
    Label(Label),
    MatchBlockSize { match_index: usize },
    MatchFirstBlockStart { match_index: usize },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ConstExpression {
    Value(ConstantValue),
    MathExpr(MathOperation, Vec<Self>),
}

impl From<usize> for ConstExpression {
    fn from(value: usize) -> Self {
        Self::Value(ConstantValue::Scalar(F::from_usize(value)))
    }
}

impl TryFrom<Expression> for ConstExpression {
    type Error = ();

    fn try_from(value: Expression) -> Result<Self, Self::Error> {
        match value {
            Expression::Value(SimpleExpr::Constant(const_expr)) => Ok(const_expr),
            Expression::Value(_) => Err(()),
            Expression::ArrayAccess { .. } => Err(()),
            Expression::MathExpr(math_expr, args) => {
                let mut const_args = Vec::new();
                for arg in args {
                    const_args.push(Self::try_from(arg)?);
                }
                Ok(Self::MathExpr(math_expr, const_args))
            }
            Expression::FunctionCall { .. } => Err(()),
            Expression::Len { .. } => Err(()),
            Expression::Lambda { .. } => Err(()),
        }
    }
}

impl ConstExpression {
    pub const fn zero() -> Self {
        Self::scalar(F::ZERO)
    }

    pub const fn one() -> Self {
        Self::scalar(F::ONE)
    }

    pub const fn label(label: Label) -> Self {
        Self::Value(ConstantValue::Label(label))
    }

    pub const fn scalar(scalar: F) -> Self {
        Self::Value(ConstantValue::Scalar(scalar))
    }

    pub fn from_usize(value: usize) -> Self {
        Self::Value(ConstantValue::Scalar(F::from_usize(value)))
    }

    pub const fn function_size(function_name: Label) -> Self {
        Self::Value(ConstantValue::FunctionSize { function_name })
    }
    pub fn eval_with<EvalFn>(&self, func: &EvalFn) -> Option<F>
    where
        EvalFn: Fn(&ConstantValue) -> Option<F>,
    {
        match self {
            Self::Value(value) => func(value),
            Self::MathExpr(math_expr, args) => {
                let mut eval_args = Vec::new();
                for arg in args {
                    eval_args.push(arg.eval_with(func)?);
                }
                Some(math_expr.eval(&eval_args))
            }
        }
    }

    pub fn naive_eval(&self) -> Option<F> {
        self.eval_with(&|value| match value {
            ConstantValue::Scalar(scalar) => Some(*scalar),
            _ => None,
        })
    }
}

impl From<ConstantValue> for ConstExpression {
    fn from(value: ConstantValue) -> Self {
        Self::Value(value)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Condition {
    AssumeBoolean(Expression),
    Comparison(BooleanExpr<Expression>),
}

impl Display for Condition {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::AssumeBoolean(expr) => write!(f, "{expr}"),
            Self::Comparison(cmp) => write!(f, "{cmp}"),
        }
    }
}

impl Condition {
    pub fn expressions_mut(&mut self) -> Vec<&mut Expression> {
        match self {
            Self::AssumeBoolean(expr) => vec![expr],
            Self::Comparison(cmp) => vec![&mut cmp.left, &mut cmp.right],
        }
    }

    pub fn eval_with(&self, eval_expr: &impl Fn(&Expression) -> Option<F>) -> Option<bool> {
        match self {
            Self::AssumeBoolean(expr) => {
                let val = eval_expr(expr)?;
                Some(val != F::ZERO)
            }
            Self::Comparison(cmp) => {
                let left = eval_expr(&cmp.left)?;
                let right = eval_expr(&cmp.right)?;
                Some(match cmp.kind {
                    Boolean::Equal => left == right,
                    Boolean::Different => left != right,
                    Boolean::LessThan => left < right,
                    Boolean::LessOrEqual => left <= right,
                })
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Expression {
    Value(SimpleExpr),
    ArrayAccess {
        array: Var,
        index: Vec<Self>, // multi-dimensional array access
    },
    MathExpr(MathOperation, Vec<Self>),
    FunctionCall {
        function_name: String,
        args: Vec<Self>,
        location: SourceLocation,
    },
    Len {
        array: String,
        indices: Vec<Self>,
    },
    /// Lambda expression: `lambda param: body`
    Lambda {
        param: Var,
        body: Box<Self>,
    },
}

/// For arbitrary compile-time computations
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MathOperation {
    /// Addition operation.
    Add,
    /// Multiplication operation.
    Mul,
    /// Subtraction operation (compiled to addition with negation).
    Sub,
    /// Division operation (compiled to multiplication with inverse).
    Div,
    /// Exponentiation (only for constant expressions).
    Exp,
    /// Modulo operation (only for constant expressions).
    Mod,
    /// Logarithm ceiling
    Log2Ceil,
    /// similar to rust's next_multiple_of
    NextMultipleOf,
    /// saturating subtraction
    SaturatingSub,
    /// Integer division with ceiling
    DivCeil,
}

impl TryFrom<MathOperation> for Operation {
    type Error = String;

    fn try_from(value: MathOperation) -> Result<Self, Self::Error> {
        match value {
            MathOperation::Add => Ok(Self::Add),
            MathOperation::Mul => Ok(Self::Mul),
            _ => Err(format!("Cannot convert {value:?} to add/mul operation")),
        }
    }
}

impl Display for MathOperation {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Add => write!(f, "add"),
            Self::Mul => write!(f, "mul"),
            Self::Sub => write!(f, "sub"),
            Self::Div => write!(f, "div"),
            Self::Exp => write!(f, "exp"),
            Self::Mod => write!(f, "mod"),
            Self::Log2Ceil => write!(f, "log2_ceil"),
            Self::NextMultipleOf => write!(f, "next_multiple_of"),
            Self::SaturatingSub => write!(f, "saturating_sub"),
            Self::DivCeil => write!(f, "div_ceil"),
        }
    }
}

impl MathOperation {
    pub fn is_unary(&self) -> bool {
        self.num_args() == 1
    }
    pub fn num_args(&self) -> usize {
        match self {
            Self::Log2Ceil => 1,
            Self::Add
            | Self::Mul
            | Self::Sub
            | Self::Div
            | Self::Exp
            | Self::Mod
            | Self::NextMultipleOf
            | Self::SaturatingSub
            | Self::DivCeil => 2,
        }
    }
    pub fn eval(&self, args: &[F]) -> F {
        assert_eq!(args.len(), self.num_args());
        match self {
            Self::Add => args[0] + args[1],
            Self::Mul => args[0] * args[1],
            Self::Sub => args[0] - args[1],
            Self::Div => args[0] / args[1],
            Self::Exp => args[0].exp_u64(args[1].as_canonical_u64()),
            Self::Mod => F::from_usize(args[0].to_usize() % args[1].to_usize()),
            Self::Log2Ceil => F::from_usize(log2_ceil_usize(args[0].to_usize())),
            Self::NextMultipleOf => {
                let value = args[0];
                let multiple = args[1];
                let value_usize = value.to_usize();
                let multiple_usize = multiple.to_usize();
                let res = value_usize.next_multiple_of(multiple_usize);
                F::from_usize(res)
            }
            Self::SaturatingSub => F::from_usize(args[0].to_usize().saturating_sub(args[1].to_usize())),
            Self::DivCeil => F::from_usize(args[0].to_usize().div_ceil(args[1].to_usize())),
        }
    }
}

impl From<SimpleExpr> for Expression {
    fn from(value: SimpleExpr) -> Self {
        Self::Value(value)
    }
}

impl Expression {
    pub fn compile_time_eval(
        &self,
        const_arrays: &BTreeMap<String, ConstArrayValue>,
        vector_len: &VectorLenTracker,
    ) -> Option<F> {
        // Handle Len specially since it needs const_arrays
        if let Self::Len { array, indices } = self {
            let idx = indices
                .iter()
                .map(|e| e.compile_time_eval(const_arrays, vector_len))
                .collect::<Option<Vec<F>>>()?;
            if let Some(arr) = const_arrays.get(array) {
                let target = arr.navigate(&idx)?;
                return Some(F::from_usize(target.len()));
            }
            if let Some(arr) = vector_len.get(array) {
                let usize_idx: Vec<usize> = idx.iter().map(|f| f.to_usize()).collect();
                let target = arr.navigate(&usize_idx)?;
                return Some(F::from_usize(target.len()));
            }
            return None;
        }
        self.eval_with(
            &|value: &SimpleExpr| value.as_constant()?.naive_eval(),
            &|arr, indexes| {
                let array = const_arrays.get(arr)?;
                assert_eq!(indexes.len(), array.depth());
                array.navigate(&indexes)?.as_scalar()
            },
        )
    }

    pub fn eval_with<ValueFn, ArrayFn>(&self, value_fn: &ValueFn, array_fn: &ArrayFn) -> Option<F>
    where
        ValueFn: Fn(&SimpleExpr) -> Option<F>,
        ArrayFn: Fn(&Var, Vec<F>) -> Option<F>,
    {
        match self {
            Self::Value(value) => value_fn(value),
            Self::ArrayAccess { array, index } => array_fn(
                array,
                index
                    .iter()
                    .map(|e| e.eval_with(value_fn, array_fn))
                    .collect::<Option<Vec<_>>>()?,
            ),
            Self::MathExpr(math_expr, args) => {
                let mut eval_args = Vec::new();
                for arg in args {
                    eval_args.push(arg.eval_with(value_fn, array_fn)?);
                }
                Some(math_expr.eval(&eval_args))
            }
            Self::FunctionCall { .. } => None,
            Self::Len { .. } => None,
            Self::Lambda { .. } => None, // Lambdas are only used in match_range, not evaluated directly
        }
    }

    pub fn inner_exprs_mut(&mut self) -> Vec<&mut Self> {
        match self {
            Self::Value(_) => vec![],
            Self::ArrayAccess { index, .. } => index.iter_mut().collect(),
            Self::MathExpr(_, args) => args.iter_mut().collect(),
            Self::FunctionCall { args, .. } => args.iter_mut().collect(),
            Self::Len { indices, .. } => indices.iter_mut().collect(),
            Self::Lambda { body, .. } => vec![body.as_mut()],
        }
    }

    pub fn inner_exprs(&self) -> Vec<&Self> {
        match self {
            Self::Value(_) => vec![],
            Self::ArrayAccess { index, .. } => index.iter().collect(),
            Self::MathExpr(_, args) => args.iter().collect(),
            Self::FunctionCall { args, .. } => args.iter().collect(),
            Self::Lambda { body, .. } => vec![body.as_ref()],
            Self::Len { indices, .. } => indices.iter().collect(),
        }
    }

    pub fn var(var: Var) -> Self {
        SimpleExpr::from(var).into()
    }

    pub fn scalar(scalar: F) -> Self {
        SimpleExpr::scalar(scalar).into()
    }

    pub fn as_scalar(&self) -> Option<F> {
        match self {
            Self::Value(SimpleExpr::Constant(ConstExpression::Value(ConstantValue::Scalar(start_val)))) => {
                Some(*start_val)
            }
            _ => None,
        }
    }

    pub fn is_scalar(&self) -> bool {
        self.as_scalar().is_some()
    }

    pub fn zero() -> Self {
        Self::scalar(F::ZERO)
    }

    pub fn one() -> Self {
        Self::scalar(F::ONE)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AssignmentTarget {
    Var { var: Var, is_mutable: bool },
    ArrayAccess { array: Var, index: Box<Expression> }, // always immutable
}

impl Display for AssignmentTarget {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Var { var, is_mutable } => {
                if *is_mutable {
                    write!(f, "{var}: Mut")
                } else {
                    write!(f, "{var}")
                }
            }
            Self::ArrayAccess { array, index } => write!(f, "{array}[{index}]"),
        }
    }
}

impl AssignmentTarget {
    pub fn index_expression_mut(&mut self) -> Option<&mut Expression> {
        match self {
            Self::Var { .. } => None,
            Self::ArrayAccess { index, .. } => Some(index),
        }
    }
}

/// A compile-time dynamic array literal: DynArray(elem1, elem2, ...)
/// Elements can be expressions or nested DynArray literals.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VecLiteral {
    /// A scalar expression element
    Expr(Expression),
    /// A nested vector literal
    Vec(Vec<VecLiteral>),
}

impl VecLiteral {
    pub fn all_exprs_mut_in_slice(arr: &mut [Self]) -> Vec<&mut Expression> {
        let mut exprs = Vec::new();
        for elem in arr {
            match elem {
                Self::Expr(expr) => exprs.push(expr),
                Self::Vec(nested) => {
                    exprs.extend(Self::all_exprs_mut_in_slice(nested));
                }
            }
        }
        exprs
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LoopKind {
    Range,
    Unroll,
    /// `for i in dynamic_unroll(0, a, n_bits): body` — unrolls over runtime-bounded range
    /// using bit decomposition. `n_bits` must be compile-time known.
    DynamicUnroll {
        n_bits: Expression,
    },
}

impl LoopKind {
    pub fn is_unroll(&self) -> bool {
        matches!(self, Self::Unroll | Self::DynamicUnroll { .. })
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Line {
    Match {
        value: Expression,
        arms: Vec<(usize, Vec<Self>)>,
        location: SourceLocation,
    },
    ForwardDeclaration {
        var: Var,
        is_mutable: bool,
    },
    Statement {
        targets: Vec<AssignmentTarget>, // LHS - can be empty for standalone calls
        value: Expression,              // RHS - any expression
        location: SourceLocation,
    },
    Assert {
        debug: bool,
        boolean: BooleanExpr<Expression>,
        location: SourceLocation,
    },
    IfCondition {
        condition: Condition,
        then_branch: Vec<Self>,
        else_branch: Vec<Self>,
        location: SourceLocation,
    },
    ForLoop {
        iterator: Var,
        start: Expression,
        end: Expression,
        body: Vec<Self>,
        loop_kind: LoopKind,
        location: SourceLocation,
    },
    FunctionRet {
        return_data: Vec<Expression>,
    },
    Panic {
        message: Option<String>,
    },
    // noop, debug purpose only
    LocationReport {
        location: SourceLocation,
    },
    /// Compile-time dynamic array declaration: var = DynArray(...)
    VecDeclaration {
        var: Var,
        elements: Vec<VecLiteral>,
        location: SourceLocation,
    },
    /// Compile-time vector push: push(vec_var, element) or push(vec_var[i][j], element)
    Push {
        vector: Var,
        indices: Vec<Expression>,
        element: VecLiteral,
        location: SourceLocation,
    },
    /// Compile-time vector pop: vec_var.pop() or vec_var[i][j].pop()
    Pop {
        vector: Var,
        indices: Vec<Expression>,
        location: SourceLocation,
    },
}

/// A context specifying which variables are in scope.
#[derive(Debug)]
pub struct Context {
    /// A list of lexical scopes, innermost scope last.
    pub scopes: Vec<Scope>,
    /// A mapping from constant array names to their values.
    pub const_arrays: BTreeMap<String, ConstArrayValue>,
}

impl Context {
    pub fn new() -> Context {
        Context {
            scopes: vec![Scope::default()],
            const_arrays: BTreeMap::new(),
        }
    }

    pub fn defines(&self, var: &Var) -> bool {
        if self.const_arrays.contains_key(var) {
            return true;
        }
        for scope in self.scopes.iter() {
            if scope.vars.contains(var) {
                return true;
            }
        }
        false
    }

    pub fn add_var(&mut self, var: &Var) {
        let last_scope = self.scopes.last_mut().unwrap();
        assert!(
            !last_scope.vars.contains(var),
            "Variable declared multiple times in the same scope: {var}",
        );
        last_scope.vars.insert(var.clone());
    }
}

#[derive(Debug, Default, Clone)]
pub struct Scope {
    /// A set of declared variables.
    pub vars: BTreeSet<Var>,
}

impl Display for Expression {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Value(val) => write!(f, "{val}"),
            Self::ArrayAccess { array, index } => {
                write!(f, "{array}[{index:?}]")
            }
            Self::MathExpr(math_expr, args) => {
                let args_str = args.iter().map(|arg| format!("{arg}")).collect::<Vec<_>>().join(", ");
                write!(f, "{math_expr}({args_str})")
            }
            Self::FunctionCall {
                function_name, args, ..
            } => {
                let args_str = args.iter().map(|arg| format!("{arg}")).collect::<Vec<_>>().join(", ");
                write!(f, "{function_name}({args_str})")
            }
            Self::Len { array, indices } => {
                let indices_str = indices.iter().map(|i| format!("[{i}]")).collect::<Vec<_>>().join("");
                write!(f, "len({array}{indices_str})")
            }
            Self::Lambda { param, body } => {
                write!(f, "lambda {param}: {body}")
            }
        }
    }
}

impl Line {
    fn to_string_with_indent(&self, indent: usize) -> String {
        let spaces = "    ".repeat(indent);
        let line_str = match self {
            Self::LocationReport { .. } => {
                // print nothing
                Default::default()
            }
            Self::Match { value, arms, .. } => {
                let arms_str = arms
                    .iter()
                    .map(|(const_expr, body)| {
                        let body_str = body
                            .iter()
                            .map(|line| line.to_string_with_indent(indent + 1))
                            .collect::<Vec<_>>()
                            .join("\n");
                        format!("case {const_expr}: {{\n{body_str}\n{spaces}}}")
                    })
                    .collect::<Vec<_>>()
                    .join("\n");
                format!("match {value}: {{\n{arms_str}\n{spaces}}}")
            }
            Self::ForwardDeclaration { var, is_mutable } => {
                if *is_mutable {
                    format!("{var}: Mut")
                } else {
                    format!("{var}: Imu")
                }
            }
            Self::Statement { targets, value, .. } => {
                if targets.is_empty() {
                    format!("{value}")
                } else {
                    let targets_str = targets
                        .iter()
                        .map(|target| target.to_string())
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!("{targets_str} = {value}")
                }
            }
            Self::Assert {
                debug,
                boolean,
                location: _,
            } => format!("{}assert {}", if *debug { "debug_" } else { "" }, boolean),
            Self::IfCondition {
                condition,
                then_branch,
                else_branch,
                location: _,
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
                    format!("if {condition} {{\n{then_str}\n{spaces}}}")
                } else {
                    format!("if {condition} {{\n{then_str}\n{spaces}}} else {{\n{else_str}\n{spaces}}}")
                }
            }
            Self::ForLoop {
                iterator,
                start,
                end,
                body,
                loop_kind,
                location: _,
            } => {
                let body_str = body
                    .iter()
                    .map(|line| line.to_string_with_indent(indent + 1))
                    .collect::<Vec<_>>()
                    .join("\n");
                match loop_kind {
                    LoopKind::DynamicUnroll { n_bits } => format!(
                        "for {} in dynamic_unroll({}, {}, {}) {{\n{}\n{}}}",
                        iterator, start, end, n_bits, body_str, spaces
                    ),
                    _ => {
                        let range_fn = if loop_kind.is_unroll() { "unroll" } else { "range" };
                        format!(
                            "for {} in {}({}, {}) {{\n{}\n{}}}",
                            iterator, range_fn, start, end, body_str, spaces
                        )
                    }
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
            Self::Panic { message } => match message {
                Some(msg) => format!("assert False, \"{msg}\""),
                None => "assert False".to_string(),
            },
            Self::VecDeclaration { var, elements, .. } => {
                format!("{var} = DynArray({})", elements.len())
            }
            Self::Push {
                vector,
                indices,
                element,
                ..
            } => {
                format!(
                    "{}[{}].push({})",
                    vector,
                    indices.iter().map(|i| format!("{i}")).collect::<Vec<_>>().join("]["),
                    element
                )
            }
            Self::Pop { vector, indices, .. } => {
                if indices.is_empty() {
                    format!("{}.pop()", vector)
                } else {
                    format!(
                        "{}[{}].pop()",
                        vector,
                        indices.iter().map(|i| format!("{i}")).collect::<Vec<_>>().join("][")
                    )
                }
            }
        };
        format!("{spaces}{line_str}")
    }

    pub fn nested_blocks(&self) -> Vec<&Vec<Line>> {
        match self {
            Self::Match { arms, .. } => arms.iter().map(|(_, body)| body).collect(),
            Self::IfCondition {
                then_branch,
                else_branch,
                ..
            } => vec![then_branch, else_branch],
            Self::ForLoop { body, .. } => vec![body],
            Self::ForwardDeclaration { .. }
            | Self::Statement { .. }
            | Self::Assert { .. }
            | Self::FunctionRet { .. }
            | Self::Panic { .. }
            | Self::LocationReport { .. }
            | Self::VecDeclaration { .. }
            | Self::Push { .. }
            | Self::Pop { .. } => vec![],
        }
    }

    pub fn nested_blocks_mut(&mut self) -> Vec<&mut Vec<Line>> {
        match self {
            Self::Match { arms, .. } => arms.iter_mut().map(|(_, body)| body).collect(),
            Self::IfCondition {
                then_branch,
                else_branch,
                ..
            } => vec![then_branch, else_branch],
            Self::ForLoop { body, .. } => vec![body],
            Self::ForwardDeclaration { .. }
            | Self::Statement { .. }
            | Self::Assert { .. }
            | Self::FunctionRet { .. }
            | Self::Panic { .. }
            | Self::LocationReport { .. }
            | Self::VecDeclaration { .. }
            | Self::Push { .. }
            | Self::Pop { .. } => vec![],
        }
    }

    /// Returns mutable references to all expressions contained in this line.
    /// Does NOT include expressions inside nested blocks (use nested_blocks_mut for those).
    pub fn expressions_mut(&mut self) -> Vec<&mut Expression> {
        match self {
            Self::Match { value, .. } => vec![value],
            Self::Statement { targets, value, .. } => {
                let mut exprs = vec![value];
                for target in targets {
                    if let Some(idx) = target.index_expression_mut() {
                        exprs.push(idx);
                    }
                }
                exprs
            }
            Self::Assert { boolean, .. } => vec![&mut boolean.left, &mut boolean.right],
            Self::IfCondition { condition, .. } => condition.expressions_mut(),
            Self::ForLoop {
                start, end, loop_kind, ..
            } => {
                let mut exprs = vec![start, end];
                if let LoopKind::DynamicUnroll { n_bits } = loop_kind {
                    exprs.push(n_bits);
                }
                exprs
            }
            Self::FunctionRet { return_data } => return_data.iter_mut().collect(),
            Self::Push { indices, element, .. } => {
                let mut exprs = indices.iter_mut().collect::<Vec<_>>();
                exprs.extend(VecLiteral::all_exprs_mut_in_slice(std::slice::from_mut(element)));
                exprs
            }
            Self::Pop { indices, .. } => indices.iter_mut().collect(),
            Self::VecDeclaration { elements, .. } => VecLiteral::all_exprs_mut_in_slice(elements),
            Self::ForwardDeclaration { .. } | Self::Panic { .. } | Self::LocationReport { .. } => vec![],
        }
    }
}

impl Display for ConstantValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Scalar(scalar) => write!(f, "{scalar}"),
            Self::FunctionSize { function_name } => {
                write!(f, "@function_size_{function_name}")
            }
            Self::Label(label) => write!(f, "{label}"),
            Self::MatchFirstBlockStart { match_index } => {
                write!(f, "@match_first_block_start_{match_index}")
            }
            Self::MatchBlockSize { match_index } => {
                write!(f, "@match_block_size_{match_index}")
            }
        }
    }
}

impl Display for VecLiteral {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Expr(expr) => write!(f, "{expr}"),
            Self::Vec(elements) => {
                let elements_str = elements
                    .iter()
                    .map(|elem| format!("{elem}"))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "DynArray([{elements_str}])")
            }
        }
    }
}

impl Display for SimpleExpr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Constant(constant) => write!(f, "{constant}"),
            Self::Memory(var_or_const_malloc_access) => write!(f, "{var_or_const_malloc_access}"),
        }
    }
}

impl Display for ConstExpression {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Value(value) => write!(f, "{value}"),
            Self::MathExpr(math_expr, args) => {
                let args_str = args.iter().map(|arg| format!("{arg}")).collect::<Vec<_>>().join(", ");
                write!(f, "{math_expr}({args_str})")
            }
        }
    }
}

impl Display for Line {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_string_with_indent(0))
    }
}

impl Display for Program {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        // Print const arrays
        for (name, value) in &self.const_arrays {
            write!(f, "const {name} = ")?;
            write_const_array_value(f, value)?;
            writeln!(f, ";")?;
        }

        let mut first = self.const_arrays.is_empty();
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

fn write_const_array_value(f: &mut Formatter<'_>, value: &ConstArrayValue) -> std::fmt::Result {
    match value {
        ConstArrayValue::Scalar(v) => write!(f, "{v}"),
        ConstArrayValue::Array(elements) => {
            write!(f, "[")?;
            for (i, elem) in elements.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write_const_array_value(f, elem)?;
            }
            write!(f, "]")
        }
    }
}

impl Display for Function {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let args_str = self
            .arguments
            .iter()
            .map(|arg| {
                if arg.is_const {
                    format!("const {}", arg.name)
                } else if arg.is_mutable {
                    format!("mut {}", arg.name)
                } else {
                    arg.name.to_string()
                }
            })
            .collect::<Vec<_>>()
            .join(", ");

        let instructions_str = self
            .body
            .iter()
            .map(|line| line.to_string_with_indent(1))
            .collect::<Vec<_>>()
            .join("\n");

        if self.body.is_empty() {
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
