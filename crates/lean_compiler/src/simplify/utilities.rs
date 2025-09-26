use crate::{
    F,
    lang::{Boolean, Expression, Line, SimpleExpr, Var},
};
use std::collections::{BTreeMap, BTreeSet};
use utils::ToUsize;

/// Returns (internal_vars, external_vars) for a sequence of lines.
pub fn find_variable_usage(lines: &[Line]) -> (BTreeSet<Var>, BTreeSet<Var>) {
    let mut internal_vars = BTreeSet::new();
    let mut external_vars = BTreeSet::new();

    let on_new_expr =
        |expr: &Expression, internal_vars: &BTreeSet<Var>, external_vars: &mut BTreeSet<Var>| {
            for var in vars_in_expression(expr) {
                if !internal_vars.contains(&var) {
                    external_vars.insert(var);
                }
            }
        };

    let on_new_condition =
        |condition: &Boolean, internal_vars: &BTreeSet<Var>, external_vars: &mut BTreeSet<Var>| {
            let (Boolean::Equal { left, right } | Boolean::Different { left, right }) = condition;
            on_new_expr(left, internal_vars, external_vars);
            on_new_expr(right, internal_vars, external_vars);
        };

    for line in lines {
        match line {
            Line::Match { value, arms } => {
                on_new_expr(value, &internal_vars, &mut external_vars);
                for (_, statements) in arms {
                    let (stmt_internal, stmt_external) = find_variable_usage(statements);
                    internal_vars.extend(stmt_internal);
                    external_vars.extend(
                        stmt_external
                            .into_iter()
                            .filter(|v| !internal_vars.contains(v)),
                    );
                }
            }
            Line::Assignment { var, value } => {
                on_new_expr(value, &internal_vars, &mut external_vars);
                internal_vars.insert(var.clone());
            }
            Line::IfCondition {
                condition,
                then_branch,
                else_branch,
            } => {
                on_new_condition(condition, &internal_vars, &mut external_vars);

                let (then_internal, then_external) = find_variable_usage(then_branch);
                let (else_internal, else_external) = find_variable_usage(else_branch);

                internal_vars.extend(then_internal.union(&else_internal).cloned());
                external_vars.extend(
                    then_external
                        .union(&else_external)
                        .filter(|v| !internal_vars.contains(*v))
                        .cloned(),
                );
            }
            Line::FunctionCall {
                args, return_data, ..
            } => {
                for arg in args {
                    on_new_expr(arg, &internal_vars, &mut external_vars);
                }
                internal_vars.extend(return_data.iter().cloned());
            }
            Line::Assert(condition) => {
                on_new_condition(condition, &internal_vars, &mut external_vars);
            }
            Line::FunctionRet { return_data } => {
                for ret in return_data {
                    on_new_expr(ret, &internal_vars, &mut external_vars);
                }
            }
            Line::MAlloc { var, size, .. } => {
                on_new_expr(size, &internal_vars, &mut external_vars);
                internal_vars.insert(var.clone());
            }
            Line::Precompile {
                precompile: _,
                args,
            } => {
                for arg in args {
                    on_new_expr(arg, &internal_vars, &mut external_vars);
                }
            }
            Line::Print { content, .. } => {
                for var in content {
                    on_new_expr(var, &internal_vars, &mut external_vars);
                }
            }
            Line::DecomposeBits { var, to_decompose } => {
                for expr in to_decompose {
                    on_new_expr(expr, &internal_vars, &mut external_vars);
                }
                internal_vars.insert(var.clone());
            }
            Line::CounterHint { var } => {
                internal_vars.insert(var.clone());
            }
            Line::ForLoop {
                iterator,
                start,
                end,
                body,
                rev: _,
                unroll: _,
            } => {
                let (body_internal, body_external) = find_variable_usage(body);
                internal_vars.extend(body_internal);
                internal_vars.insert(iterator.clone());
                external_vars.extend(body_external.difference(&internal_vars).cloned());
                on_new_expr(start, &internal_vars, &mut external_vars);
                on_new_expr(end, &internal_vars, &mut external_vars);
            }
            Line::ArrayAssign {
                array,
                index,
                value,
            } => {
                on_new_expr(&array.clone().into(), &internal_vars, &mut external_vars);
                on_new_expr(index, &internal_vars, &mut external_vars);
                on_new_expr(value, &internal_vars, &mut external_vars);
            }
            Line::Panic | Line::Break | Line::LocationReport { .. } => {}
        }
    }

    (internal_vars, external_vars)
}

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

/// Replace variables with constants in a line sequence.
pub fn replace_vars_by_const_in_lines(lines: &mut [Line], map: &BTreeMap<Var, F>) {
    for line in lines {
        match line {
            Line::Match { value, arms } => {
                replace_vars_by_const_in_expr(value, map);
                for (_, statements) in arms {
                    replace_vars_by_const_in_lines(statements, map);
                }
            }
            Line::Assignment { var, value } => {
                assert!(!map.contains_key(var), "Variable {var} is a constant");
                replace_vars_by_const_in_expr(value, map);
            }
            Line::ArrayAssign {
                array,
                index,
                value,
            } => {
                if let SimpleExpr::Var(array_var) = array {
                    assert!(
                        !map.contains_key(array_var),
                        "Array {array_var} is a constant"
                    );
                }
                replace_vars_by_const_in_expr(index, map);
                replace_vars_by_const_in_expr(value, map);
            }
            Line::FunctionCall {
                args, return_data, ..
            } => {
                for arg in args {
                    replace_vars_by_const_in_expr(arg, map);
                }
                for ret in return_data {
                    assert!(
                        !map.contains_key(ret),
                        "Return variable {ret} is a constant"
                    );
                }
            }
            Line::IfCondition {
                condition,
                then_branch,
                else_branch,
            } => {
                match condition {
                    Boolean::Equal { left, right } | Boolean::Different { left, right } => {
                        replace_vars_by_const_in_expr(left, map);
                        replace_vars_by_const_in_expr(right, map);
                    }
                }
                replace_vars_by_const_in_lines(then_branch, map);
                replace_vars_by_const_in_lines(else_branch, map);
            }
            Line::ForLoop {
                body, start, end, ..
            } => {
                replace_vars_by_const_in_expr(start, map);
                replace_vars_by_const_in_expr(end, map);
                replace_vars_by_const_in_lines(body, map);
            }
            Line::Assert(condition) => match condition {
                Boolean::Equal { left, right } | Boolean::Different { left, right } => {
                    replace_vars_by_const_in_expr(left, map);
                    replace_vars_by_const_in_expr(right, map);
                }
            },
            Line::FunctionRet { return_data } => {
                for ret in return_data {
                    replace_vars_by_const_in_expr(ret, map);
                }
            }
            Line::Precompile {
                precompile: _,
                args,
            } => {
                for arg in args {
                    replace_vars_by_const_in_expr(arg, map);
                }
            }
            Line::Print { content, .. } => {
                for var in content {
                    replace_vars_by_const_in_expr(var, map);
                }
            }
            Line::DecomposeBits { var, to_decompose } => {
                assert!(!map.contains_key(var), "Variable {var} is a constant");
                for expr in to_decompose {
                    replace_vars_by_const_in_expr(expr, map);
                }
            }
            Line::CounterHint { var } => {
                assert!(!map.contains_key(var), "Variable {var} is a constant");
            }
            Line::MAlloc { var, size, .. } => {
                assert!(!map.contains_key(var), "Variable {var} is a constant");
                replace_vars_by_const_in_expr(size, map);
            }
            Line::Panic | Line::Break | Line::LocationReport { .. } => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::{Boolean, Expression, Line, SimpleExpr};
    use p3_field::PrimeCharacteristicRing;
    use std::collections::{BTreeMap, BTreeSet};

    #[test]
    fn test_find_variable_usage_empty() {
        let lines: Vec<Line> = vec![];
        let (internal, external) = find_variable_usage(&lines);

        assert!(internal.is_empty());
        assert!(external.is_empty());
    }

    #[test]
    fn test_find_variable_usage_assignment() {
        let lines = vec![Line::Assignment {
            var: "x".to_string(),
            value: Expression::scalar(42),
        }];
        let (internal, external) = find_variable_usage(&lines);

        assert_eq!(internal, BTreeSet::from(["x".to_string()]));
        assert!(external.is_empty());
    }

    #[test]
    fn test_find_variable_usage_assignment_with_external_var() {
        let lines = vec![Line::Assignment {
            var: "x".to_string(),
            value: Expression::Value(SimpleExpr::Var("y".to_string())),
        }];
        let (internal, external) = find_variable_usage(&lines);

        assert_eq!(internal, BTreeSet::from(["x".to_string()]));
        assert_eq!(external, BTreeSet::from(["y".to_string()]));
    }

    #[test]
    fn test_find_variable_usage_function_call() {
        let lines = vec![Line::FunctionCall {
            function_name: "test".to_string(),
            args: vec![Expression::Value(SimpleExpr::Var("input".to_string()))],
            return_data: vec!["output".to_string()],
        }];
        let (internal, external) = find_variable_usage(&lines);

        assert_eq!(internal, BTreeSet::from(["output".to_string()]));
        assert_eq!(external, BTreeSet::from(["input".to_string()]));
    }

    #[test]
    fn test_find_variable_usage_if_condition() {
        let lines = vec![Line::IfCondition {
            condition: Boolean::Equal {
                left: Expression::Value(SimpleExpr::Var("a".to_string())),
                right: Expression::scalar(10),
            },
            then_branch: vec![Line::Assignment {
                var: "b".to_string(),
                value: Expression::scalar(1),
            }],
            else_branch: vec![Line::Assignment {
                var: "c".to_string(),
                value: Expression::scalar(2),
            }],
        }];
        let (internal, external) = find_variable_usage(&lines);

        assert_eq!(internal, BTreeSet::from(["b".to_string(), "c".to_string()]));
        assert_eq!(external, BTreeSet::from(["a".to_string()]));
    }

    #[test]
    fn test_find_variable_usage_for_loop() {
        let lines = vec![Line::ForLoop {
            iterator: "i".to_string(),
            start: Expression::scalar(0),
            end: Expression::Value(SimpleExpr::Var("n".to_string())),
            body: vec![Line::Assignment {
                var: "sum".to_string(),
                value: Expression::Binary {
                    left: Box::new(Expression::Value(SimpleExpr::Var("sum".to_string()))),
                    operation: crate::ir::HighLevelOperation::Add,
                    right: Box::new(Expression::Value(SimpleExpr::Var("i".to_string()))),
                },
            }],
            rev: false,
            unroll: false,
        }];
        let (internal, external) = find_variable_usage(&lines);

        assert_eq!(
            internal,
            BTreeSet::from(["i".to_string(), "sum".to_string()])
        );
        assert_eq!(external, BTreeSet::from(["n".to_string()]));
    }

    #[test]
    fn test_find_variable_usage_match() {
        let lines = vec![Line::Match {
            value: Expression::Value(SimpleExpr::Var("x".to_string())),
            arms: vec![
                (
                    0,
                    vec![Line::Assignment {
                        var: "a".to_string(),
                        value: Expression::scalar(1),
                    }],
                ),
                (
                    1,
                    vec![Line::Assignment {
                        var: "b".to_string(),
                        value: Expression::scalar(2),
                    }],
                ),
            ],
        }];
        let (internal, external) = find_variable_usage(&lines);

        assert_eq!(internal, BTreeSet::from(["a".to_string(), "b".to_string()]));
        assert_eq!(external, BTreeSet::from(["x".to_string()]));
    }

    #[test]
    fn test_find_variable_usage_malloc() {
        let lines = vec![Line::MAlloc {
            var: "ptr".to_string(),
            size: Expression::Value(SimpleExpr::Var("size".to_string())),
            vectorized: false,
            vectorized_len: Expression::zero(),
        }];
        let (internal, external) = find_variable_usage(&lines);

        assert_eq!(internal, BTreeSet::from(["ptr".to_string()]));
        assert_eq!(external, BTreeSet::from(["size".to_string()]));
    }

    #[test]
    fn test_find_variable_usage_decompose_bits() {
        let lines = vec![Line::DecomposeBits {
            var: "bits".to_string(),
            to_decompose: vec![Expression::Value(SimpleExpr::Var("value".to_string()))],
        }];
        let (internal, external) = find_variable_usage(&lines);

        assert_eq!(internal, BTreeSet::from(["bits".to_string()]));
        assert_eq!(external, BTreeSet::from(["value".to_string()]));
    }

    #[test]
    fn test_find_variable_usage_counter_hint() {
        let lines = vec![Line::CounterHint {
            var: "counter".to_string(),
        }];
        let (internal, external) = find_variable_usage(&lines);

        assert_eq!(internal, BTreeSet::from(["counter".to_string()]));
        assert!(external.is_empty());
    }

    #[test]
    fn test_find_variable_usage_assert() {
        let lines = vec![Line::Assert(Boolean::Different {
            left: Expression::Value(SimpleExpr::Var("x".to_string())),
            right: Expression::Value(SimpleExpr::Var("y".to_string())),
        })];
        let (internal, external) = find_variable_usage(&lines);

        assert!(internal.is_empty());
        assert_eq!(external, BTreeSet::from(["x".to_string(), "y".to_string()]));
    }

    #[test]
    fn test_find_variable_usage_function_ret() {
        let lines = vec![Line::FunctionRet {
            return_data: vec![Expression::Value(SimpleExpr::Var("result".to_string()))],
        }];
        let (internal, external) = find_variable_usage(&lines);

        assert!(internal.is_empty());
        assert_eq!(external, BTreeSet::from(["result".to_string()]));
    }

    #[test]
    fn test_find_variable_usage_precompile() {
        let lines = vec![Line::Precompile {
            precompile: crate::precompiles::PRECOMPILES[0].clone(),
            args: vec![Expression::Value(SimpleExpr::Var("input".to_string()))],
        }];
        let (internal, external) = find_variable_usage(&lines);

        assert!(internal.is_empty());
        assert_eq!(external, BTreeSet::from(["input".to_string()]));
    }

    #[test]
    fn test_find_variable_usage_print() {
        let lines = vec![Line::Print {
            line_info: "debug".to_string(),
            content: vec![Expression::Value(SimpleExpr::Var("debug_var".to_string()))],
        }];
        let (internal, external) = find_variable_usage(&lines);

        assert!(internal.is_empty());
        assert_eq!(external, BTreeSet::from(["debug_var".to_string()]));
    }

    #[test]
    fn test_find_variable_usage_array_assign() {
        let lines = vec![Line::ArrayAssign {
            array: SimpleExpr::Var("arr".to_string()),
            index: Expression::Value(SimpleExpr::Var("idx".to_string())),
            value: Expression::Value(SimpleExpr::Var("val".to_string())),
        }];
        let (internal, external) = find_variable_usage(&lines);

        assert!(internal.is_empty());
        assert_eq!(
            external,
            BTreeSet::from(["arr".to_string(), "idx".to_string(), "val".to_string()])
        );
    }

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

    #[test]
    fn test_get_function_called_empty() {
        let lines: Vec<Line> = vec![];
        let mut function_called = Vec::new();

        get_function_called(&lines, &mut function_called);

        assert!(function_called.is_empty());
    }

    #[test]
    fn test_get_function_called_function_call() {
        let lines = vec![Line::FunctionCall {
            function_name: "test_func".to_string(),
            args: vec![],
            return_data: vec![],
        }];
        let mut function_called = Vec::new();

        get_function_called(&lines, &mut function_called);

        assert_eq!(function_called, vec!["test_func".to_string()]);
    }

    #[test]
    fn test_get_function_called_multiple_calls() {
        let lines = vec![
            Line::FunctionCall {
                function_name: "func1".to_string(),
                args: vec![],
                return_data: vec![],
            },
            Line::Assignment {
                var: "x".to_string(),
                value: Expression::scalar(42),
            },
            Line::FunctionCall {
                function_name: "func2".to_string(),
                args: vec![],
                return_data: vec![],
            },
        ];
        let mut function_called = Vec::new();

        get_function_called(&lines, &mut function_called);

        assert_eq!(
            function_called,
            vec!["func1".to_string(), "func2".to_string()]
        );
    }

    #[test]
    fn test_get_function_called_if_condition() {
        let lines = vec![Line::IfCondition {
            condition: Boolean::Equal {
                left: Expression::scalar(1),
                right: Expression::scalar(1),
            },
            then_branch: vec![Line::FunctionCall {
                function_name: "then_func".to_string(),
                args: vec![],
                return_data: vec![],
            }],
            else_branch: vec![Line::FunctionCall {
                function_name: "else_func".to_string(),
                args: vec![],
                return_data: vec![],
            }],
        }];
        let mut function_called = Vec::new();

        get_function_called(&lines, &mut function_called);

        assert_eq!(
            function_called,
            vec!["then_func".to_string(), "else_func".to_string()]
        );
    }

    #[test]
    fn test_get_function_called_for_loop() {
        let lines = vec![Line::ForLoop {
            iterator: "i".to_string(),
            start: Expression::scalar(0),
            end: Expression::scalar(10),
            body: vec![Line::FunctionCall {
                function_name: "loop_func".to_string(),
                args: vec![],
                return_data: vec![],
            }],
            rev: false,
            unroll: false,
        }];
        let mut function_called = Vec::new();

        get_function_called(&lines, &mut function_called);

        assert_eq!(function_called, vec!["loop_func".to_string()]);
    }

    #[test]
    fn test_get_function_called_match() {
        let lines = vec![Line::Match {
            value: Expression::scalar(1),
            arms: vec![
                (
                    0,
                    vec![Line::FunctionCall {
                        function_name: "arm0_func".to_string(),
                        args: vec![],
                        return_data: vec![],
                    }],
                ),
                (
                    1,
                    vec![Line::FunctionCall {
                        function_name: "arm1_func".to_string(),
                        args: vec![],
                        return_data: vec![],
                    }],
                ),
            ],
        }];
        let mut function_called = Vec::new();

        get_function_called(&lines, &mut function_called);

        assert_eq!(
            function_called,
            vec!["arm0_func".to_string(), "arm1_func".to_string()]
        );
    }

    #[test]
    fn test_replace_vars_by_const_in_lines_assignment() {
        let mut lines = vec![Line::Assignment {
            var: "y".to_string(),
            value: Expression::Value(SimpleExpr::Var("x".to_string())),
        }];
        let mut map = BTreeMap::new();
        map.insert("x".to_string(), crate::F::from_usize(42));

        replace_vars_by_const_in_lines(&mut lines, &map);

        assert_eq!(
            lines,
            vec![Line::Assignment {
                var: "y".to_string(),
                value: Expression::scalar(42),
            }]
        );
    }

    #[test]
    fn test_replace_vars_by_const_in_lines_function_call() {
        let mut lines = vec![Line::FunctionCall {
            function_name: "test".to_string(),
            args: vec![Expression::Value(SimpleExpr::Var("x".to_string()))],
            return_data: vec!["result".to_string()],
        }];
        let mut map = BTreeMap::new();
        map.insert("x".to_string(), crate::F::from_usize(100));

        replace_vars_by_const_in_lines(&mut lines, &map);

        assert_eq!(
            lines,
            vec![Line::FunctionCall {
                function_name: "test".to_string(),
                args: vec![Expression::scalar(100)],
                return_data: vec!["result".to_string()],
            }]
        );
    }

    #[test]
    fn test_replace_vars_by_const_in_lines_if_condition() {
        let mut lines = vec![Line::IfCondition {
            condition: Boolean::Equal {
                left: Expression::Value(SimpleExpr::Var("x".to_string())),
                right: Expression::scalar(10),
            },
            then_branch: vec![Line::Assignment {
                var: "y".to_string(),
                value: Expression::Value(SimpleExpr::Var("x".to_string())),
            }],
            else_branch: vec![],
        }];
        let mut map = BTreeMap::new();
        map.insert("x".to_string(), crate::F::from_usize(5));

        replace_vars_by_const_in_lines(&mut lines, &map);

        assert_eq!(
            lines,
            vec![Line::IfCondition {
                condition: Boolean::Equal {
                    left: Expression::scalar(5),
                    right: Expression::scalar(10),
                },
                then_branch: vec![Line::Assignment {
                    var: "y".to_string(),
                    value: Expression::scalar(5),
                }],
                else_branch: vec![],
            }]
        );
    }
}

/// Extract function calls from line sequence.
pub fn get_function_called(lines: &[Line], function_called: &mut Vec<String>) {
    for line in lines {
        match line {
            Line::Match { value: _, arms } => {
                for (_, statements) in arms {
                    get_function_called(statements, function_called);
                }
            }
            Line::FunctionCall { function_name, .. } => {
                function_called.push(function_name.clone());
            }
            Line::IfCondition {
                then_branch,
                else_branch,
                ..
            } => {
                get_function_called(then_branch, function_called);
                get_function_called(else_branch, function_called);
            }
            Line::ForLoop { body, .. } => {
                get_function_called(body, function_called);
            }
            Line::Assignment { .. }
            | Line::ArrayAssign { .. }
            | Line::Assert { .. }
            | Line::FunctionRet { .. }
            | Line::Precompile { .. }
            | Line::Print { .. }
            | Line::DecomposeBits { .. }
            | Line::CounterHint { .. }
            | Line::MAlloc { .. }
            | Line::Panic
            | Line::Break
            | Line::LocationReport { .. } => {}
        }
    }
}
