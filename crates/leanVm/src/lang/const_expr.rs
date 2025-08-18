use std::fmt;

use p3_field::PrimeCharacteristicRing;

use crate::{
    Label,
    lang::{ConstantValue, F, HighLevelOperation, SimpleExpr, expression::Expression},
};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ConstExpression {
    Value(ConstantValue),
    Binary {
        left: Box<Self>,
        operation: HighLevelOperation,
        right: Box<Self>,
    },
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

impl From<ConstantValue> for ConstExpression {
    fn from(value: ConstantValue) -> Self {
        Self::Value(value)
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
