//! Expression types for the AST.

use p3_field::PrimeCharacteristicRing;
use p3_util::log2_ceil_usize;
use std::fmt::{Display, Formatter};

use crate::{F, ir::HighLevelOperation};
use crate::lang::values::{ConstExpression, ConstantValue, Var, ConstMallocLabel};
use utils::ToUsize;

/// Simple expression that can be a variable, constant, or memory access.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SimpleExpr {
    /// Variable reference.
    Var(Var),
    /// Constant value.
    Constant(ConstExpression),
    /// Access to const malloc memory.
    ConstMallocAccess {
        malloc_label: ConstMallocLabel,
        offset: ConstExpression,
    },
}

impl SimpleExpr {
    /// Creates a zero constant.
    pub fn zero() -> Self {
        Self::scalar(0)
    }

    /// Creates a one constant.
    pub fn one() -> Self {
        Self::scalar(1)
    }

    /// Creates a scalar constant.
    pub fn scalar(scalar: usize) -> Self {
        Self::Constant(ConstantValue::Scalar(scalar).into())
    }

    /// Returns true if this expression is a constant.
    pub const fn is_constant(&self) -> bool {
        matches!(self, Self::Constant(_))
    }

    /// Simplifies the expression if it's a constant.
    pub fn simplify_if_const(&self) -> Self {
        if let Self::Constant(constant) = self {
            return constant.try_naive_simplification().into();
        }
        self.clone()
    }

    /// Extracts the constant expression if this is a constant.
    pub fn as_constant(&self) -> Option<ConstExpression> {
        match self {
            Self::Var(_) => None,
            Self::Constant(constant) => Some(constant.clone()),
            Self::ConstMallocAccess { .. } => None,
        }
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

/// Complex expression supporting operations and array access.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Expression {
    /// Simple value expression.
    Value(SimpleExpr),
    /// Array element access.
    ArrayAccess {
        array: SimpleExpr,
        index: Box<Expression>,
    },
    /// Binary operation.
    Binary {
        left: Box<Self>,
        operation: HighLevelOperation,
        right: Box<Self>,
    },
    /// Ceiling of log base 2.
    Log2Ceil {
        value: Box<Expression>,
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
    /// Evaluates the expression if it contains only constants.
    pub fn naive_eval(&self) -> Option<F> {
        self.eval_with(
            &|value: &SimpleExpr| value.as_constant()?.naive_eval(),
            &|_, _| None,
        )
    }

    /// Evaluates the expression with custom value and array functions.
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
            Self::Log2Ceil { value } => {
                let value = value.eval_with(value_fn, array_fn)?;
                Some(F::from_usize(log2_ceil_usize(value.to_usize())))
            }
        }
    }

    /// Creates a scalar expression.
    pub fn scalar(scalar: usize) -> Self {
        SimpleExpr::scalar(scalar).into()
    }

    /// Creates a zero expression.
    pub fn zero() -> Self {
        Self::scalar(0)
    }
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
            Self::Log2Ceil { value } => {
                write!(f, "log2_ceil({value})")
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