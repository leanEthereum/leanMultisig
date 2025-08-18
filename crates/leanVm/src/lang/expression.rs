use std::fmt;

use crate::{
    constant::F,
    intermediate_bytecode::HighLevelOperation,
    lang::{Var, simple_expr::SimpleExpr},
};

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
