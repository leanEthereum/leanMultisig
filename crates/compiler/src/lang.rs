use p3_field::PrimeCharacteristicRing;
use std::collections::BTreeMap;
use std::fmt::{Display, Formatter};
use utils::ToUsize;
use vm::*;

use crate::{F, intermediate_bytecode::HighLevelOperation, precompiles::Precompile};

#[derive(Debug, Clone)]
pub struct Program {
    pub functions: BTreeMap<String, Function>,
}

#[derive(Debug, Clone)]
pub struct Function {
    pub name: String,
    pub arguments: Vec<(Var, bool)>, // (name, is_const)
    pub inlined: bool,
    pub n_returned_vars: usize,
    pub body: Vec<Line>,
}

impl Function {
    pub fn has_const_arguments(&self) -> bool {
        self.arguments.iter().any(|(_, is_const)| *is_const)
    }
}

pub type Var = String;
pub type ConstMallocLabel = usize;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SimpleExpr {
    Var(Var),
    Constant(ConstExpression),
    ConstMallocAccess {
        malloc_label: ConstMallocLabel,
        offset: ConstExpression,
    },
}

impl SimpleExpr {
    pub fn zero() -> Self {
        Self::scalar(0)
    }

    pub fn one() -> Self {
        Self::scalar(1)
    }

    pub fn scalar(scalar: usize) -> Self {
        Self::Constant(ConstantValue::Scalar(scalar).into())
    }

    pub const fn is_constant(&self) -> bool {
        matches!(self, Self::Constant(_))
    }

    pub fn simplify_if_const(&self) -> Self {
        if let Self::Constant(constant) = self {
            return constant.try_naive_simplification().into();
        }
        self.clone()
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
        Self::Var(var)
    }
}

impl SimpleExpr {
    pub fn as_constant(&self) -> Option<ConstExpression> {
        match self {
            Self::Var(_) => None,
            Self::Constant(constant) => Some(constant.clone()),
            Self::ConstMallocAccess { .. } => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Boolean {
    Equal { left: Expression, right: Expression },
    Different { left: Expression, right: Expression },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ConstantValue {
    Scalar(usize),
    PublicInputStart,
    PointerToZeroVector, // In the memory of chunks of 8 field elements
    PointerToOneVector,  // In the memory of chunks of 8 field elements
    FunctionSize { function_name: Label },
    Label(Label),
    MatchBlockSize { match_index: usize },
    MatchFirstBlockStart { match_index: usize },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ConstExpression {
    Value(ConstantValue),
    Binary {
        left: Box<Self>,
        operation: HighLevelOperation,
        right: Box<Self>,
    },
}

impl From<usize> for ConstExpression {
    fn from(value: usize) -> Self {
        Self::Value(ConstantValue::Scalar(value))
    }
}

impl TryFrom<Expression> for ConstExpression {
    type Error = ();

    fn try_from(value: Expression) -> Result<Self, Self::Error> {
        match value {
            Expression::Value(SimpleExpr::Constant(const_expr)) => Ok(const_expr),
            Expression::Value(_) => Err(()),
            Expression::ArrayAccess { .. } => Err(()),
            Expression::Binary {
                left,
                operation,
                right,
            } => {
                let left_expr = Self::try_from(*left)?;
                let right_expr = Self::try_from(*right)?;
                Ok(Self::Binary {
                    left: Box::new(left_expr),
                    operation,
                    right: Box::new(right_expr),
                })
            }
        }
    }
}

impl ConstExpression {
    pub const fn zero() -> Self {
        Self::scalar(0)
    }

    pub const fn one() -> Self {
        Self::scalar(1)
    }

    pub const fn label(label: Label) -> Self {
        Self::Value(ConstantValue::Label(label))
    }

    pub const fn scalar(scalar: usize) -> Self {
        Self::Value(ConstantValue::Scalar(scalar))
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
            Self::Binary {
                left,
                operation,
                right,
            } => Some(operation.eval(left.eval_with(func)?, right.eval_with(func)?)),
        }
    }

    pub fn naive_eval(&self) -> Option<F> {
        self.eval_with(&|value| match value {
            ConstantValue::Scalar(scalar) => Some(F::from_usize(*scalar)),
            _ => None,
        })
    }

    pub fn try_naive_simplification(&self) -> Self {
        if let Some(value) = self.naive_eval() {
            Self::scalar(value.to_usize())
        } else {
            self.clone()
        }
    }
}

impl From<ConstantValue> for ConstExpression {
    fn from(value: ConstantValue) -> Self {
        Self::Value(value)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Expression {
    Value(SimpleExpr),
    ArrayAccess {
        array: SimpleExpr,
        index: Box<Expression>,
    },
    Binary {
        left: Box<Self>,
        operation: HighLevelOperation,
        right: Box<Self>,
    },
}

impl From<SimpleExpr> for Expression {
    fn from(value: SimpleExpr) -> Self {
        Self::Value(value)
    }
}

impl From<Var> for Expression {
    fn from(var: Var) -> Self {
        Self::Value(var.into())
    }
}

impl Expression {
    pub fn naive_eval(&self) -> Option<F> {
        self.eval_with(
            &|value: &SimpleExpr| value.as_constant()?.naive_eval(),
            &|_, _| None,
        )
    }

    pub fn eval_with<ValueFn, ArrayFn>(&self, value_fn: &ValueFn, array_fn: &ArrayFn) -> Option<F>
    where
        ValueFn: Fn(&SimpleExpr) -> Option<F>,
        ArrayFn: Fn(&SimpleExpr, F) -> Option<F>,
    {
        match self {
            Self::Value(value) => value_fn(value),
            Self::ArrayAccess { array, index } => {
                array_fn(array, index.eval_with(value_fn, array_fn)?)
            }
            Self::Binary {
                left,
                operation,
                right,
            } => Some(operation.eval(
                left.eval_with(value_fn, array_fn)?,
                right.eval_with(value_fn, array_fn)?,
            )),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Line {
    Match {
        value: Expression,
        arms: Vec<(usize, Vec<Self>)>,
    },
    Assignment {
        var: Var,
        value: Expression,
    },
    ArrayAssign {
        // array[index] = value
        array: SimpleExpr,
        index: Expression,
        value: Expression,
    },
    Assert(Boolean),
    IfCondition {
        condition: Boolean,
        then_branch: Vec<Self>,
        else_branch: Vec<Self>,
    },
    ForLoop {
        iterator: Var,
        start: Expression,
        end: Expression,
        body: Vec<Self>,
        rev: bool,
        unroll: bool,
    },
    FunctionCall {
        function_name: String,
        args: Vec<Expression>,
        return_data: Vec<Var>,
    },
    FunctionRet {
        return_data: Vec<Expression>,
    },
    Precompile {
        precompile: Precompile,
        args: Vec<Expression>,
    },
    Break,
    Panic,
    // Hints:
    Print {
        line_info: String,
        content: Vec<Expression>,
    },
    MAlloc {
        var: Var,
        size: Expression,
        vectorized: bool,
    },
    DecomposeBits {
        var: Var, // a pointer to 31 * len(to_decompose) field elements, containing the bits of "to_decompose"
        to_decompose: Vec<Expression>,
    },
    CounterHint {
        var: Var,
    },
    // noop, debug purpose only
    LocationReport {
        location: LocationInSourceCode,
    },
}
impl Display for Expression {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Value(val) => write!(f, "{val}"),
            Self::ArrayAccess { array, index } => {
                write!(f, "{array}[{index}]")
            }
            Self::Binary {
                left,
                operation,
                right,
            } => {
                write!(f, "({left} {operation} {right})")
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
            Self::Match { value, arms } => {
                let arms_str = arms
                    .iter()
                    .map(|(const_expr, body)| {
                        let body_str = body
                            .iter()
                            .map(|line| line.to_string_with_indent(indent + 1))
                            .collect::<Vec<_>>()
                            .join("\n");
                        format!("{const_expr} => {{\n{body_str}\n{spaces}}}")
                    })
                    .collect::<Vec<_>>()
                    .join("\n");
                format!("match {value} {{\n{arms_str}\n{spaces}}}")
            }
            Self::Assignment { var, value } => {
                format!("{var} = {value}")
            }
            Self::ArrayAssign {
                array,
                index,
                value,
            } => {
                format!("{array}[{index}] = {value}")
            }
            Self::Assert(condition) => format!("assert {condition}"),
            Self::IfCondition {
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
                    format!("if {condition} {{\n{then_str}\n{spaces}}}")
                } else {
                    format!(
                        "if {condition} {{\n{then_str}\n{spaces}}} else {{\n{else_str}\n{spaces}}}"
                    )
                }
            }
            Self::CounterHint { var } => {
                format!("{var} = counter_hint({var})")
            }
            Self::ForLoop {
                iterator,
                start,
                end,
                body,
                rev,
                unroll,
            } => {
                let body_str = body
                    .iter()
                    .map(|line| line.to_string_with_indent(indent + 1))
                    .collect::<Vec<_>>()
                    .join("\n");
                format!(
                    "for {} in {}{}..{} {}{{\n{}\n{}}}",
                    iterator,
                    start,
                    if *rev { "rev " } else { "" },
                    end,
                    if *unroll { "unroll " } else { "" },
                    body_str,
                    spaces
                )
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
                    precompile.name,
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
            Self::MAlloc {
                var,
                size,
                vectorized,
            } => {
                if *vectorized {
                    format!("{var} = malloc_vectorized({size})")
                } else {
                    format!("{var} = malloc({size})")
                }
            }
            Self::DecomposeBits { var, to_decompose } => {
                format!(
                    "{} = decompose_bits({})",
                    var,
                    to_decompose
                        .iter()
                        .map(|expr| expr.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            Self::Break => "break".to_string(),
            Self::Panic => "panic".to_string(),
        };
        format!("{spaces}{line_str}")
    }
}

impl Display for Boolean {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Equal { left, right } => {
                write!(f, "{left} == {right}")
            }
            Self::Different { left, right } => {
                write!(f, "{left} != {right}")
            }
        }
    }
}

impl Display for ConstantValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Scalar(scalar) => write!(f, "{scalar}"),
            Self::PublicInputStart => write!(f, "@public_input_start"),
            Self::PointerToZeroVector => write!(f, "@pointer_to_zero_vector"),
            Self::PointerToOneVector => write!(f, "@pointer_to_one_vector"),
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

impl Display for SimpleExpr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Var(var) => write!(f, "{var}"),
            Self::Constant(constant) => write!(f, "{constant}"),
            Self::ConstMallocAccess {
                malloc_label,
                offset,
            } => {
                write!(f, "malloc_access({malloc_label}, {offset})")
            }
        }
    }
}

impl Display for ConstExpression {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Value(value) => write!(f, "{value}"),
            Self::Binary {
                left,
                operation,
                right,
            } => {
                write!(f, "({left} {operation} {right})")
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

impl Display for Function {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let args_str = self
            .arguments
            .iter()
            .map(|arg| match arg {
                (name, true) => format!("const {name}"),
                (name, false) => name.to_string(),
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
