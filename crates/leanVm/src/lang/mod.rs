use std::fmt;

use p3_field::PrimeCharacteristicRing;

use crate::{
    Label, bytecode::precompiles::Precompile, constant::F,
    intermediate_bytecode::HighLevelOperation, lang::simple_expr::SimpleExpr,
};

pub mod function;
pub mod program;
pub mod simple_expr;

pub type Var = String;
pub type ConstMallocLabel = usize;

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
    FunctionSize { function_name: Label },
    Label(Label),
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
            Expression::Value(_) | Expression::ArrayAccess { .. } => Err(()),
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
    #[must_use]
    pub const fn zero() -> Self {
        Self::scalar(0)
    }

    #[must_use]
    pub const fn one() -> Self {
        Self::scalar(1)
    }

    #[must_use]
    pub const fn label(label: Label) -> Self {
        Self::Value(ConstantValue::Label(label))
    }

    #[must_use]
    pub const fn scalar(scalar: usize) -> Self {
        Self::Value(ConstantValue::Scalar(scalar))
    }

    #[must_use]
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

    #[must_use]
    pub fn naive_eval(&self) -> Option<F> {
        self.eval_with(&|value| match value {
            ConstantValue::Scalar(scalar) => Some(F::from_usize(*scalar)),
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
pub enum Expression {
    Value(SimpleExpr),
    ArrayAccess {
        array: Var,
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
    #[must_use]
    pub fn naive_eval(&self) -> Option<F> {
        self.eval_with(
            &|value: &SimpleExpr| value.as_constant()?.naive_eval(),
            &|_, _| None,
        )
    }

    pub fn eval_with<ValueFn, ArrayFn>(&self, value_fn: &ValueFn, array_fn: &ArrayFn) -> Option<F>
    where
        ValueFn: Fn(&SimpleExpr) -> Option<F>,
        ArrayFn: Fn(&Var, F) -> Option<F>,
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
    Assignment {
        var: Var,
        value: Expression,
    },
    ArrayAssign {
        // array[index] = value
        array: Var,
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
        res: Vec<Var>,
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
        var: Var, // a pointer to 31 field elements, containing the bits of "to_decompose"
        to_decompose: Expression,
    },
}

impl fmt::Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Value(val) => write!(f, "{val}"),
            Self::ArrayAccess { array, index } => write!(f, "{array}[{index}]"),
            Self::Binary {
                left,
                operation,
                right,
            } => write!(f, "({left} {operation} {right})"),
        }
    }
}

impl Line {
    #[allow(clippy::too_many_lines)]
    fn to_string_with_indent(&self, indent: usize) -> String {
        let spaces = "    ".repeat(indent);
        let line_str = match self {
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
            Self::ForLoop {
                iterator,
                start,
                end,
                body,
                unroll,
            } => {
                let body_str = body
                    .iter()
                    .map(|line| line.to_string_with_indent(indent + 1))
                    .collect::<Vec<_>>()
                    .join("\n");
                format!(
                    "for {} in {}..{} {}{{\n{}\n{}}}",
                    iterator,
                    start,
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
                    .map(std::string::ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ");
                let return_data_str = return_data
                    .iter()
                    .map(std::string::ToString::to_string)
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
                    .map(std::string::ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("return {return_data_str}")
            }
            Self::Precompile {
                precompile,
                args,
                res: return_data,
            } => {
                format!(
                    "{} = {}({})",
                    return_data
                        .iter()
                        .map(std::string::ToString::to_string)
                        .collect::<Vec<_>>()
                        .join(", "),
                    precompile.name,
                    args.iter()
                        .map(std::string::ToString::to_string)
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
                    .map(std::string::ToString::to_string)
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
                format!("{var} = decompose_bits({to_decompose})")
            }
            Self::Break => "break".to_string(),
            Self::Panic => "panic".to_string(),
        };
        format!("{spaces}{line_str}")
    }
}

impl fmt::Display for Boolean {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Equal { left, right } => write!(f, "{left} == {right}"),
            Self::Different { left, right } => write!(f, "{left} != {right}"),
        }
    }
}

impl fmt::Display for ConstantValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Scalar(scalar) => write!(f, "{scalar}"),
            Self::PublicInputStart => write!(f, "@public_input_start"),
            Self::PointerToZeroVector => write!(f, "@pointer_to_zero_vector"),
            Self::FunctionSize { function_name } => {
                write!(f, "@function_size_{function_name}")
            }
            Self::Label(label) => write!(f, "{label}"),
        }
    }
}

impl fmt::Display for ConstExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Value(value) => write!(f, "{value}"),
            Self::Binary {
                left,
                operation,
                right,
            } => write!(f, "({left} {operation} {right})"),
        }
    }
}

impl fmt::Display for Line {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_string_with_indent(0))
    }
}
