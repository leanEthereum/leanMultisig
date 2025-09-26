//! Expression types for the AST.

use crate::ir::IntermediaryMemOrFpOrConstant;
use p3_field::PrimeCharacteristicRing;
use p3_util::log2_ceil_usize;
use std::fmt::{Display, Formatter};

use crate::lang::values::{ConstExpression, ConstMallocLabel, ConstantValue, Var};
use crate::{F, ir::HighLevelOperation};
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

    /// Converts this SimpleExpr to an IntermediaryMemOrFpOrConstant for code generation.
    pub fn to_mem_after_fp_or_constant(
        &self,
        compiler: &crate::codegen::Compiler,
    ) -> IntermediaryMemOrFpOrConstant {
        match self {
            Self::Var(var) => IntermediaryMemOrFpOrConstant::MemoryAfterFp {
                offset: compiler.get_offset(&var.clone().into()),
            },
            Self::Constant(c) => IntermediaryMemOrFpOrConstant::Constant(c.clone()),
            Self::ConstMallocAccess {
                malloc_label,
                offset,
            } => IntermediaryMemOrFpOrConstant::MemoryAfterFp {
                offset: compiler.get_offset(
                    &crate::simplify::VarOrConstMallocAccess::ConstMallocAccess {
                        malloc_label: *malloc_label,
                        offset: offset.clone(),
                    },
                ),
            },
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
    Log2Ceil { value: Box<Expression> },
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::IntermediaryMemOrFpOrConstant;
    use crate::lang::ConstExpression;

    #[test]
    fn test_simple_expr_constants() {
        assert!(SimpleExpr::zero().is_constant());
        assert!(SimpleExpr::one().is_constant());
        assert!(SimpleExpr::scalar(42).is_constant());
        assert!(!SimpleExpr::Var("x".to_string()).is_constant());
    }

    #[test]
    fn test_simple_expr_as_constant() {
        let var = SimpleExpr::Var("x".to_string());
        let constant = SimpleExpr::scalar(5);

        assert_eq!(var.as_constant(), None);
        assert_eq!(constant.as_constant(), Some(ConstExpression::scalar(5)));
    }

    #[test]
    fn test_expression_scalar_creation() {
        let expr = Expression::scalar(10);
        assert_eq!(expr.naive_eval().unwrap().to_usize(), 10);
    }

    #[test]
    fn test_simple_expr_display() {
        assert_eq!(SimpleExpr::Var("x".to_string()).to_string(), "x");
        assert_eq!(SimpleExpr::scalar(42).to_string(), "42");

        let malloc_access = SimpleExpr::ConstMallocAccess {
            malloc_label: 5,
            offset: ConstExpression::scalar(10),
        };
        assert_eq!(malloc_access.to_string(), "malloc_access(5, 10)");
    }

    #[test]
    fn test_expression_display() {
        let var = Expression::Value(SimpleExpr::Var("x".to_string()));
        assert_eq!(var.to_string(), "x");

        let array_access = Expression::ArrayAccess {
            array: SimpleExpr::Var("arr".to_string()),
            index: Box::new(Expression::scalar(0)),
        };
        assert_eq!(array_access.to_string(), "arr[0]");

        let log2_ceil = Expression::Log2Ceil {
            value: Box::new(Expression::scalar(8)),
        };
        assert_eq!(log2_ceil.to_string(), "log2_ceil(8)");

        let binary = Expression::Binary {
            left: Box::new(Expression::scalar(5)),
            operation: crate::ir::HighLevelOperation::Mul,
            right: Box::new(Expression::scalar(2)),
        };
        assert_eq!(binary.to_string(), "(5 * 2)");
    }

    #[test]
    fn test_expression_eval_with() {
        let value_fn = |expr: &SimpleExpr| match expr {
            SimpleExpr::Var(name) if name == "x" => Some(F::from_usize(10)),
            SimpleExpr::Constant(c) => c.naive_eval(),
            _ => None,
        };
        let array_fn = |array: &SimpleExpr, index: F| -> Option<F> {
            if matches!(array, SimpleExpr::Var(name) if name == "arr") {
                Some(F::from_usize(index.to_usize() * 2))
            } else {
                None
            }
        };

        // Test Value variant
        let var_expr = Expression::Value(SimpleExpr::Var("x".to_string()));
        assert_eq!(
            var_expr.eval_with(&value_fn, &array_fn).unwrap().to_usize(),
            10
        );

        // Test ArrayAccess variant
        let array_expr = Expression::ArrayAccess {
            array: SimpleExpr::Var("arr".to_string()),
            index: Box::new(Expression::scalar(5)),
        };
        assert_eq!(
            array_expr
                .eval_with(&value_fn, &array_fn)
                .unwrap()
                .to_usize(),
            10
        );

        // Test Binary variant
        let binary_expr = Expression::Binary {
            left: Box::new(Expression::scalar(3)),
            operation: crate::ir::HighLevelOperation::Add,
            right: Box::new(Expression::scalar(7)),
        };
        assert_eq!(
            binary_expr
                .eval_with(&value_fn, &array_fn)
                .unwrap()
                .to_usize(),
            10
        );

        // Test Log2Ceil variant
        let log2_expr = Expression::Log2Ceil {
            value: Box::new(Expression::scalar(8)),
        };
        assert_eq!(
            log2_expr
                .eval_with(&value_fn, &array_fn)
                .unwrap()
                .to_usize(),
            3
        );
    }

    #[test]
    fn test_simple_expr_simplify_if_const() {
        let var = SimpleExpr::Var("x".to_string());
        let simplified_var = var.simplify_if_const();
        assert_eq!(simplified_var, var);

        let constant = SimpleExpr::scalar(42);
        let simplified_constant = constant.simplify_if_const();
        assert_eq!(simplified_constant, SimpleExpr::scalar(42));
    }

    #[test]
    fn test_simple_expr_to_mem_after_fp_or_constant() {
        let mut compiler = crate::codegen::Compiler::new();
        compiler.var_positions.insert("x".to_string(), 5);
        compiler.const_mallocs.insert(0, 10);

        // Test variable conversion
        let var_expr = SimpleExpr::Var("x".to_string());
        let result = var_expr.to_mem_after_fp_or_constant(&compiler);
        if let IntermediaryMemOrFpOrConstant::MemoryAfterFp { offset } = result {
            assert_eq!(offset, ConstExpression::scalar(5));
        } else {
            panic!("Expected MemoryAfterFp variant");
        }

        // Test constant conversion
        let const_expr = SimpleExpr::scalar(42);
        let result = const_expr.to_mem_after_fp_or_constant(&compiler);
        if let IntermediaryMemOrFpOrConstant::Constant(const_expr) = result {
            assert_eq!(const_expr, ConstExpression::scalar(42));
        } else {
            panic!("Expected Constant variant");
        }

        // Test const malloc access conversion
        let malloc_expr = SimpleExpr::ConstMallocAccess {
            malloc_label: 0,
            offset: ConstExpression::scalar(3),
        };
        let result = malloc_expr.to_mem_after_fp_or_constant(&compiler);
        if let IntermediaryMemOrFpOrConstant::MemoryAfterFp { offset } = result {
            // Should be 10 + 3 = 13
            if let ConstExpression::Binary {
                operation,
                left,
                right,
            } = offset
            {
                assert_eq!(operation, crate::ir::HighLevelOperation::Add);
                assert_eq!(left.as_ref(), &ConstExpression::scalar(10));
                assert_eq!(right.as_ref(), &ConstExpression::scalar(3));
            } else {
                panic!("Expected binary expression for const malloc access");
            }
        } else {
            panic!("Expected MemoryAfterFp variant");
        }
    }

    #[test]
    #[should_panic(expected = "Variable y not in scope")]
    fn test_simple_expr_to_mem_after_fp_or_constant_unknown_var() {
        let compiler = crate::codegen::Compiler::new();

        let var_expr = SimpleExpr::Var("y".to_string());
        let _result = var_expr.to_mem_after_fp_or_constant(&compiler);
    }

    #[test]
    #[should_panic(expected = "Const malloc 1 not in scope")]
    fn test_simple_expr_to_mem_after_fp_or_constant_unknown_malloc() {
        let compiler = crate::codegen::Compiler::new();

        let malloc_expr = SimpleExpr::ConstMallocAccess {
            malloc_label: 1,
            offset: ConstExpression::scalar(0),
        };
        let _result = malloc_expr.to_mem_after_fp_or_constant(&compiler);
    }
}
