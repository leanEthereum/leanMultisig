use crate::lang::{Expression, SimpleExpr};
use crate::{F, lang::Var};
use std::collections::{BTreeMap, BTreeSet};
use utils::ToUsize;

/// Extract all variables referenced in an expression.
pub fn vars_in_expression(expr: &Expression) -> BTreeSet<Var> {
    let mut vars = BTreeSet::new();
    match expr {
        Expression::Value(value) => {
            if let SimpleExpr::Var(var) = value {
                vars.insert(var.clone());
            }
        }
        Expression::ArrayAccess { array, index } => {
            if let SimpleExpr::Var(array) = array {
                vars.insert(array.clone());
            }
            vars.extend(vars_in_expression(index));
        }
        Expression::Binary { left, right, .. } => {
            vars.extend(vars_in_expression(left));
            vars.extend(vars_in_expression(right));
        }
        Expression::Log2Ceil { value } => {
            vars.extend(vars_in_expression(value));
        }
    }
    vars
}

/// Replace variables with constants in an expression.
pub fn replace_vars_by_const_in_expr(expr: &mut Expression, map: &BTreeMap<Var, F>) {
    match expr {
        Expression::Value(value) => match &value {
            SimpleExpr::Var(var) => {
                if let Some(const_value) = map.get(var) {
                    *value = SimpleExpr::scalar(const_value.to_usize());
                }
            }
            SimpleExpr::ConstMallocAccess { .. } => {
                unreachable!()
            }
            SimpleExpr::Constant(_) => {}
        },
        Expression::ArrayAccess { array, index } => {
            if let SimpleExpr::Var(array_var) = array {
                assert!(
                    !map.contains_key(array_var),
                    "Array {array_var} is a constant"
                );
            }
            replace_vars_by_const_in_expr(index, map);
        }
        Expression::Binary { left, right, .. } => {
            replace_vars_by_const_in_expr(left, map);
            replace_vars_by_const_in_expr(right, map);
        }
        Expression::Log2Ceil { value } => {
            replace_vars_by_const_in_expr(value, map);
        }
    }
}

/// Extract function calls from a single expression.
/// Note: In this AST design, function calls are statements, not expressions,
/// so this function only traverses sub-expressions without finding any function calls.
#[allow(clippy::only_used_in_recursion)]
pub fn get_function_calls_in_expr(expr: &Expression, function_calls: &mut Vec<String>) {
    match expr {
        Expression::Value(_) => {}
        Expression::Binary { left, right, .. } => {
            get_function_calls_in_expr(left, function_calls);
            get_function_calls_in_expr(right, function_calls);
        }
        Expression::ArrayAccess { index, .. } => {
            get_function_calls_in_expr(index, function_calls);
        }
        Expression::Log2Ceil { value } => {
            get_function_calls_in_expr(value, function_calls);
        }
    }
}

/// Find internal and external variables in a single expression.
pub fn find_internal_vars_in_expr(expr: &Expression) -> (BTreeSet<Var>, BTreeSet<Var>) {
    let vars = vars_in_expression(expr);
    (BTreeSet::new(), vars)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::SimpleExpr;
    use p3_field::PrimeCharacteristicRing;
    use std::collections::{BTreeMap, BTreeSet};

    #[test]
    fn test_vars_in_expression_value() {
        let expr = Expression::Value(SimpleExpr::Var("x".to_string()));
        let vars = vars_in_expression(&expr);

        assert_eq!(vars, BTreeSet::from(["x".to_string()]));
    }

    #[test]
    fn test_vars_in_expression_constant() {
        let expr = Expression::scalar(42);
        let vars = vars_in_expression(&expr);

        assert!(vars.is_empty());
    }

    #[test]
    fn test_vars_in_expression_binary() {
        let expr = Expression::Binary {
            left: Box::new(Expression::Value(SimpleExpr::Var("a".to_string()))),
            operation: crate::ir::HighLevelOperation::Add,
            right: Box::new(Expression::Value(SimpleExpr::Var("b".to_string()))),
        };
        let vars = vars_in_expression(&expr);

        assert_eq!(vars, BTreeSet::from(["a".to_string(), "b".to_string()]));
    }

    #[test]
    fn test_vars_in_expression_array_access() {
        let expr = Expression::ArrayAccess {
            array: SimpleExpr::Var("arr".to_string()),
            index: Box::new(Expression::Value(SimpleExpr::Var("idx".to_string()))),
        };
        let vars = vars_in_expression(&expr);

        assert_eq!(vars, BTreeSet::from(["arr".to_string(), "idx".to_string()]));
    }

    #[test]
    fn test_vars_in_expression_log2_ceil() {
        let expr = Expression::Log2Ceil {
            value: Box::new(Expression::Value(SimpleExpr::Var("n".to_string()))),
        };
        let vars = vars_in_expression(&expr);

        assert_eq!(vars, BTreeSet::from(["n".to_string()]));
    }

    #[test]
    fn test_vars_in_expression_nested() {
        let expr = Expression::Binary {
            left: Box::new(Expression::ArrayAccess {
                array: SimpleExpr::Var("arr".to_string()),
                index: Box::new(Expression::Value(SimpleExpr::Var("i".to_string()))),
            }),
            operation: crate::ir::HighLevelOperation::Mul,
            right: Box::new(Expression::Binary {
                left: Box::new(Expression::Value(SimpleExpr::Var("x".to_string()))),
                operation: crate::ir::HighLevelOperation::Add,
                right: Box::new(Expression::Value(SimpleExpr::Var("y".to_string()))),
            }),
        };
        let vars = vars_in_expression(&expr);

        assert_eq!(
            vars,
            BTreeSet::from([
                "arr".to_string(),
                "i".to_string(),
                "x".to_string(),
                "y".to_string()
            ])
        );
    }

    #[test]
    fn test_replace_vars_by_const_in_expr_var_replacement() {
        let mut expr = Expression::Value(SimpleExpr::Var("x".to_string()));
        let mut map = BTreeMap::new();
        map.insert("x".to_string(), crate::F::from_usize(42));

        replace_vars_by_const_in_expr(&mut expr, &map);

        assert_eq!(expr, Expression::scalar(42));
    }

    #[test]
    fn test_replace_vars_by_const_in_expr_no_replacement() {
        let mut expr = Expression::Value(SimpleExpr::Var("y".to_string()));
        let mut map = BTreeMap::new();
        map.insert("x".to_string(), crate::F::from_usize(42));

        replace_vars_by_const_in_expr(&mut expr, &map);

        assert_eq!(expr, Expression::Value(SimpleExpr::Var("y".to_string())));
    }

    #[test]
    fn test_replace_vars_by_const_in_expr_constant_unchanged() {
        let mut expr = Expression::scalar(100);
        let mut map = BTreeMap::new();
        map.insert("x".to_string(), crate::F::from_usize(42));

        replace_vars_by_const_in_expr(&mut expr, &map);

        assert_eq!(expr, Expression::scalar(100));
    }

    #[test]
    fn test_replace_vars_by_const_in_expr_binary() {
        let mut expr = Expression::Binary {
            left: Box::new(Expression::Value(SimpleExpr::Var("x".to_string()))),
            operation: crate::ir::HighLevelOperation::Add,
            right: Box::new(Expression::Value(SimpleExpr::Var("y".to_string()))),
        };
        let mut map = BTreeMap::new();
        map.insert("x".to_string(), crate::F::from_usize(10));
        map.insert("y".to_string(), crate::F::from_usize(20));

        replace_vars_by_const_in_expr(&mut expr, &map);

        assert_eq!(
            expr,
            Expression::Binary {
                left: Box::new(Expression::scalar(10)),
                operation: crate::ir::HighLevelOperation::Add,
                right: Box::new(Expression::scalar(20)),
            }
        );
    }

    #[test]
    fn test_replace_vars_by_const_in_expr_log2_ceil() {
        let mut expr = Expression::Log2Ceil {
            value: Box::new(Expression::Value(SimpleExpr::Var("n".to_string()))),
        };
        let mut map = BTreeMap::new();
        map.insert("n".to_string(), crate::F::from_usize(16));

        replace_vars_by_const_in_expr(&mut expr, &map);

        assert_eq!(
            expr,
            Expression::Log2Ceil {
                value: Box::new(Expression::scalar(16)),
            }
        );
    }
}
