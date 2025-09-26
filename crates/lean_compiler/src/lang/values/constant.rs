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

#[cfg(test)]
mod tests {
    use super::*;
    use lean_vm::Label;

    #[test]
    fn test_const_expression_constructors() {
        let zero = ConstExpression::zero();
        let one = ConstExpression::one();
        let scalar = ConstExpression::scalar(42);

        assert_eq!(zero.naive_eval().unwrap().to_usize(), 0);
        assert_eq!(one.naive_eval().unwrap().to_usize(), 1);
        assert_eq!(scalar.naive_eval().unwrap().to_usize(), 42);
    }

    #[test]
    fn test_const_expression_simplification() {
        let expr = ConstExpression::scalar(10);
        let simplified = expr.try_naive_simplification();
        assert_eq!(simplified.naive_eval().unwrap().to_usize(), 10);
    }

    #[test]
    fn test_constant_value_display() {
        assert_eq!(ConstantValue::Scalar(42).to_string(), "42");
        assert_eq!(
            ConstantValue::PublicInputStart.to_string(),
            "@public_input_start"
        );
        assert_eq!(
            ConstantValue::PointerToZeroVector.to_string(),
            "@pointer_to_zero_vector"
        );
        assert_eq!(
            ConstantValue::PointerToOneVector.to_string(),
            "@pointer_to_one_vector"
        );
        assert_eq!(
            ConstantValue::MatchBlockSize { match_index: 5 }.to_string(),
            "@match_block_size_5"
        );
        assert_eq!(
            ConstantValue::MatchFirstBlockStart { match_index: 3 }.to_string(),
            "@match_first_block_start_3"
        );

        let label = Label::function("test");
        assert_eq!(
            ConstantValue::FunctionSize { function_name: label.clone() }.to_string(),
            format!("@function_size_{}", label)
        );
    }

    #[test]
    fn test_const_expression_display() {
        let value = ConstExpression::Value(ConstantValue::Scalar(42));
        assert_eq!(value.to_string(), "42");

        let log2_expr = ConstExpression::Log2Ceil {
            value: Box::new(ConstExpression::scalar(8)),
        };
        assert_eq!(log2_expr.to_string(), "log2_ceil(8)");

        let binary_expr = ConstExpression::Binary {
            left: Box::new(ConstExpression::scalar(5)),
            operation: crate::ir::HighLevelOperation::Add,
            right: Box::new(ConstExpression::scalar(3)),
        };
        assert_eq!(binary_expr.to_string(), "(5 + 3)");
    }

    #[test]
    fn test_const_expression_from_usize() {
        let expr = ConstExpression::from(100);
        assert_eq!(expr.naive_eval().unwrap().to_usize(), 100);
    }

    #[test]
    fn test_constant_value_label() {
        let label = Label::function("test_func");
        let const_val = ConstantValue::Label(label.clone());
        assert_eq!(const_val.to_string(), label.to_string());
    }

    #[test]
    fn test_const_expression_eval_with() {
        let eval_fn = |value: &ConstantValue| match value {
            ConstantValue::Scalar(n) => Some(F::from_usize(*n)),
            ConstantValue::PublicInputStart => Some(F::from_usize(1000)),
            _ => None,
        };

        // Test Value variant
        let scalar = ConstExpression::Value(ConstantValue::Scalar(42));
        assert_eq!(scalar.eval_with(&eval_fn).unwrap().to_usize(), 42);

        // Test Binary variant
        let binary = ConstExpression::Binary {
            left: Box::new(ConstExpression::scalar(5)),
            operation: crate::ir::HighLevelOperation::Mul,
            right: Box::new(ConstExpression::scalar(3)),
        };
        assert_eq!(binary.eval_with(&eval_fn).unwrap().to_usize(), 15);

        // Test Log2Ceil variant
        let log2 = ConstExpression::Log2Ceil {
            value: Box::new(ConstExpression::scalar(16)),
        };
        assert_eq!(log2.eval_with(&eval_fn).unwrap().to_usize(), 4);
    }

    #[test]
    fn test_const_expression_function_size() {
        let label = Label::function("test_fn");
        let func_size = ConstExpression::function_size(label.clone());
        assert_eq!(func_size, ConstExpression::Value(ConstantValue::FunctionSize { function_name: label }));
    }

    #[test]
    fn test_const_expression_label() {
        let label = Label::function("main");
        let label_expr = ConstExpression::label(label.clone());
        assert_eq!(label_expr, ConstExpression::Value(ConstantValue::Label(label)));
    }

    #[test]
    fn test_const_expression_try_from() {
        use crate::lang::ast::{Expression, SimpleExpr};

        // Test successful conversion
        let const_expr = ConstExpression::scalar(10);
        let expr = Expression::Value(SimpleExpr::Constant(const_expr.clone()));
        let result = ConstExpression::try_from(expr);
        assert_eq!(result, Ok(const_expr));

        // Test failed conversion
        let var_expr = Expression::Value(SimpleExpr::Var("x".to_string()));
        let result = ConstExpression::try_from(var_expr);
        assert_eq!(result, Err(()));
    }
}
