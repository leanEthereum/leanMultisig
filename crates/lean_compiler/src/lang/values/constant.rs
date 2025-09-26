use lean_vm::Label;
use p3_field::PrimeCharacteristicRing;
use p3_util::log2_ceil_usize;
use std::fmt::{Display, Formatter};
use utils::ToUsize;

use crate::{F, ir::HighLevelOperation};

/// Constant value types for compile-time computation.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ConstantValue {
    Scalar(usize),
    PublicInputStart,
    PointerToZeroVector,
    PointerToOneVector,
    FunctionSize { function_name: Label },
    Label(Label),
    MatchBlockSize { match_index: usize },
    MatchFirstBlockStart { match_index: usize },
}

/// Constant expression that can be evaluated at compile time.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ConstExpression {
    Value(ConstantValue),
    Binary {
        left: Box<Self>,
        operation: HighLevelOperation,
        right: Box<Self>,
    },
    Log2Ceil {
        value: Box<Self>,
    },
}

impl From<usize> for ConstExpression {
    fn from(value: usize) -> Self {
        Self::Value(ConstantValue::Scalar(value))
    }
}

impl From<ConstantValue> for ConstExpression {
    fn from(value: ConstantValue) -> Self {
        Self::Value(value)
    }
}

impl ConstExpression {
    /// Creates a zero constant.
    pub const fn zero() -> Self {
        Self::scalar(0)
    }

    /// Creates a one constant.
    pub const fn one() -> Self {
        Self::scalar(1)
    }

    /// Creates a label constant.
    pub const fn label(label: Label) -> Self {
        Self::Value(ConstantValue::Label(label))
    }

    /// Creates a scalar constant.
    pub const fn scalar(scalar: usize) -> Self {
        Self::Value(ConstantValue::Scalar(scalar))
    }

    /// Creates a function size constant.
    pub const fn function_size(function_name: Label) -> Self {
        Self::Value(ConstantValue::FunctionSize { function_name })
    }

    /// Evaluates the constant expression with a custom evaluation function.
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
            Self::Log2Ceil { value } => {
                let value = value.eval_with(func)?;
                Some(F::from_usize(log2_ceil_usize(value.to_usize())))
            }
        }
    }

    /// Evaluates the expression if it contains only scalar values.
    pub fn naive_eval(&self) -> Option<F> {
        self.eval_with(&|value| match value {
            ConstantValue::Scalar(scalar) => Some(F::from_usize(*scalar)),
            _ => None,
        })
    }

    /// Simplifies the expression by evaluating scalar subexpressions.
    pub fn try_naive_simplification(&self) -> Self {
        if let Some(value) = self.naive_eval() {
            Self::scalar(value.to_usize())
        } else {
            self.clone()
        }
    }
}

// For supporting conversion from Expression to ConstExpression
impl TryFrom<crate::lang::ast::Expression> for ConstExpression {
    type Error = ();

    fn try_from(value: crate::lang::ast::Expression) -> Result<Self, Self::Error> {
        use crate::lang::ast::{Expression, SimpleExpr};
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
            Expression::Log2Ceil { value } => {
                let value_expr = Self::try_from(*value)?;
                Ok(Self::Log2Ceil {
                    value: Box::new(value_expr),
                })
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
            Self::Log2Ceil { value } => {
                write!(f, "log2_ceil({value})")
            }
        }
    }
}
