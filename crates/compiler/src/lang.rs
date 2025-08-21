use std::collections::BTreeMap;

use p3_field::PrimeCharacteristicRing;
use utils::ToUsize;
use vm::Label;

use crate::{F, intermediate_bytecode::HighLevelOperation, precompiles::Precompile};

#[derive(Debug, Clone)]
pub(crate) struct Program {
    pub functions: BTreeMap<String, Function>,
}

#[derive(Debug, Clone)]
pub(crate) struct Function {
    pub name: String,
    pub arguments: Vec<(Var, bool)>, // (name, is_const)
    pub n_returned_vars: usize,
    pub body: Vec<Line>,
}

impl Function {
    pub(crate) fn has_const_arguments(&self) -> bool {
        self.arguments.iter().any(|(_, is_const)| *is_const)
    }
}

pub(crate) type Var = String;
pub(crate) type ConstMallocLabel = usize;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum SimpleExpr {
    Var(Var),
    Constant(ConstExpression),
    ConstMallocAccess {
        malloc_label: ConstMallocLabel,
        offset: ConstExpression,
    },
}

impl SimpleExpr {
    pub(crate) fn zero() -> Self {
        Self::scalar(0)
    }

    pub(crate) fn one() -> Self {
        Self::scalar(1)
    }

    pub(crate) fn scalar(scalar: usize) -> Self {
        Self::Constant(ConstantValue::Scalar(scalar).into())
    }

    pub(crate) const fn is_constant(&self) -> bool {
        matches!(self, Self::Constant(_))
    }

    pub(crate) fn simplify_if_const(&self) -> Self {
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
    pub(crate) fn as_constant(&self) -> Option<ConstExpression> {
        match self {
            Self::Var(_) | Self::ConstMallocAccess { .. } => None,
            Self::Constant(constant) => Some(constant.clone()),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Boolean {
    Equal { left: Expression, right: Expression },
    Different { left: Expression, right: Expression },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum ConstantValue {
    Scalar(usize),
    PublicInputStart,
    PointerToZeroVector, // In the memory of chunks of 8 field elements
    FunctionSize { function_name: Label },
    Label(Label),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum ConstExpression {
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
    pub(crate) const fn zero() -> Self {
        Self::scalar(0)
    }

    pub(crate) const fn one() -> Self {
        Self::scalar(1)
    }

    pub(crate) const fn label(label: Label) -> Self {
        Self::Value(ConstantValue::Label(label))
    }

    pub(crate) const fn scalar(scalar: usize) -> Self {
        Self::Value(ConstantValue::Scalar(scalar))
    }

    pub(crate) const fn function_size(function_name: Label) -> Self {
        Self::Value(ConstantValue::FunctionSize { function_name })
    }

    pub(crate) fn eval_with<EvalFn>(&self, func: &EvalFn) -> Option<F>
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

    pub(crate) fn naive_eval(&self) -> Option<F> {
        self.eval_with(&|value| match value {
            ConstantValue::Scalar(scalar) => Some(F::from_usize(*scalar)),
            _ => None,
        })
    }

    pub(crate) fn try_naive_simplification(&self) -> Self {
        self.naive_eval()
            .map_or_else(|| self.clone(), |value| Self::scalar(value.to_usize()))
    }
}

impl From<ConstantValue> for ConstExpression {
    fn from(value: ConstantValue) -> Self {
        Self::Value(value)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Expression {
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
    pub(crate) fn naive_eval(&self) -> Option<F> {
        self.eval_with(
            &|value: &SimpleExpr| value.as_constant()?.naive_eval(),
            &|_, _| None,
        )
    }

    pub(crate) fn eval_with<ValueFn, ArrayFn>(
        &self,
        value_fn: &ValueFn,
        array_fn: &ArrayFn,
    ) -> Option<F>
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
pub(crate) enum Line {
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

impl ToString for Expression {
    fn to_string(&self) -> String {
        match self {
            Self::Value(val) => val.to_string(),
            Self::ArrayAccess { array, index } => {
                format!("{}[{}]", array, index.to_string())
            }
            Self::Binary {
                left,
                operation,
                right,
            } => {
                format!(
                    "({} {} {})",
                    left.to_string(),
                    operation.to_string(),
                    right.to_string()
                )
            }
        }
    }
}

impl Line {
    fn to_string_with_indent(&self, indent: usize) -> String {
        let spaces = "    ".repeat(indent);
        let line_str = match self {
            Self::Assignment { var, value } => {
                format!("{} = {}", var, value.to_string())
            }
            Self::ArrayAssign {
                array,
                index,
                value,
            } => {
                format!("{}[{}] = {}", array, index.to_string(), value.to_string())
            }
            Self::Assert(condition) => format!("assert {}", condition.to_string()),
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
                    format!(
                        "if {} {{\n{}\n{}}}",
                        condition.to_string(),
                        then_str,
                        spaces
                    )
                } else {
                    format!(
                        "if {} {{\n{}\n{}}} else {{\n{}\n{}}}",
                        condition.to_string(),
                        then_str,
                        spaces,
                        else_str,
                        spaces
                    )
                }
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
                    start.to_string(),
                    if *rev { "rev " } else { "" },
                    end.to_string(),
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
                    precompile.name.to_string(),
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
                    format!("{} = malloc_vectorized({})", var, size.to_string())
                } else {
                    format!("{} = malloc({})", var, size.to_string())
                }
            }
            Self::DecomposeBits { var, to_decompose } => {
                format!("{} = decompose_bits({})", var, to_decompose.to_string())
            }
            Self::Break => "break".to_string(),
            Self::Panic => "panic".to_string(),
        };
        format!("{spaces}{line_str}")
    }
}

impl ToString for Boolean {
    fn to_string(&self) -> String {
        match self {
            Self::Equal { left, right } => {
                format!("{} == {}", left.to_string(), right.to_string())
            }
            Self::Different { left, right } => {
                format!("{} != {}", left.to_string(), right.to_string())
            }
        }
    }
}

impl ToString for ConstantValue {
    fn to_string(&self) -> String {
        match self {
            Self::Scalar(scalar) => scalar.to_string(),
            Self::PublicInputStart => "@public_input_start".to_string(),
            Self::PointerToZeroVector => "@pointer_to_zero_vector".to_string(),
            Self::FunctionSize { function_name } => {
                format!("@function_size_{function_name}")
            }
            Self::Label(label) => label.to_string(),
        }
    }
}

impl ToString for SimpleExpr {
    fn to_string(&self) -> String {
        match self {
            Self::Var(var) => var.to_string(),
            Self::Constant(constant) => constant.to_string(),
            Self::ConstMallocAccess {
                malloc_label,
                offset,
            } => {
                format!("malloc_access({}, {})", malloc_label, offset.to_string())
            }
        }
    }
}

impl ToString for ConstExpression {
    fn to_string(&self) -> String {
        match self {
            Self::Value(value) => value.to_string(),
            Self::Binary {
                left,
                operation,
                right,
            } => {
                format!(
                    "({} {} {})",
                    left.to_string(),
                    operation.to_string(),
                    right.to_string()
                )
            }
        }
    }
}

impl ToString for Line {
    fn to_string(&self) -> String {
        self.to_string_with_indent(0)
    }
}

impl ToString for Program {
    fn to_string(&self) -> String {
        let mut result = String::new();
        for (i, function) in self.functions.values().enumerate() {
            if i > 0 {
                result.push('\n');
            }
            result.push_str(&function.to_string());
        }
        result
    }
}

impl ToString for Function {
    fn to_string(&self) -> String {
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
            format!(
                "fn {}({}) -> {} {{}}",
                self.name, args_str, self.n_returned_vars
            )
        } else {
            format!(
                "fn {}({}) -> {} {{\n{}\n}}",
                self.name, args_str, self.n_returned_vars, instructions_str
            )
        }
    }
}
