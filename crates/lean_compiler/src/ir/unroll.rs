use crate::lang::{
    ConstExpression, Expression, Line, SimpleExpr, Var, ast::statement::traits::StatementAnalysis,
};
use std::collections::BTreeSet;

/// Replace variables for unrolling in an expression.
pub fn replace_vars_for_unroll_in_expr(
    expr: &mut Expression,
    iterator: &Var,
    unroll_index: usize,
    iterator_value: usize,
    internal_vars: &BTreeSet<Var>,
) {
    match expr {
        Expression::Value(value_expr) => match value_expr {
            SimpleExpr::Var(var) => {
                if var == iterator {
                    *value_expr = SimpleExpr::Constant(ConstExpression::from(iterator_value));
                } else if internal_vars.contains(var) {
                    *var = format!("@unrolled_{unroll_index}_{iterator_value}_{var}");
                }
            }
            SimpleExpr::Constant(_) | SimpleExpr::ConstMallocAccess { .. } => {}
        },
        Expression::ArrayAccess { array, index } => {
            if let SimpleExpr::Var(array_var) = array {
                assert!(array_var != iterator, "Weird");
                if internal_vars.contains(array_var) {
                    *array_var = format!("@unrolled_{unroll_index}_{iterator_value}_{array_var}");
                }
            }

            replace_vars_for_unroll_in_expr(
                index,
                iterator,
                unroll_index,
                iterator_value,
                internal_vars,
            );
        }
        Expression::Binary { left, right, .. } => {
            replace_vars_for_unroll_in_expr(
                left,
                iterator,
                unroll_index,
                iterator_value,
                internal_vars,
            );
            replace_vars_for_unroll_in_expr(
                right,
                iterator,
                unroll_index,
                iterator_value,
                internal_vars,
            );
        }
        Expression::Log2Ceil { value } => {
            replace_vars_for_unroll_in_expr(
                value,
                iterator,
                unroll_index,
                iterator_value,
                internal_vars,
            );
        }
    }
}

/// Replace variables for unrolling in a line sequence.
pub fn replace_vars_for_unroll(
    lines: &mut [Line],
    iterator: &Var,
    unroll_index: usize,
    iterator_value: usize,
    internal_vars: &BTreeSet<Var>,
) {
    for line in lines {
        line.replace_vars_for_unroll(iterator, unroll_index, iterator_value, internal_vars);
    }
}

#[cfg(test)]
mod tests {
    use crate::lang;
    use crate::lang::{
        ArrayAssign, Assert, Assignment, Break, CounterHint, DecomposeBits, FunctionCall,
        FunctionRet, IfCondition, LocationReport, MAlloc, Panic, PrecompileStmt, Print,
    };

    use super::*;

    #[test]
    fn test_replace_vars_for_unroll_in_expr_value_iterator_replacement() {
        let mut expr = Expression::Value(SimpleExpr::Var("i".to_string()));
        let iterator = "i".to_string();
        let internal_vars = BTreeSet::new();

        replace_vars_for_unroll_in_expr(&mut expr, &iterator, 0, 5, &internal_vars);

        assert_eq!(expr, Expression::scalar(5));
    }

    #[test]
    fn test_replace_vars_for_unroll_in_expr_value_internal_var() {
        let mut expr = Expression::Value(SimpleExpr::Var("x".to_string()));
        let iterator = "i".to_string();
        let mut internal_vars = BTreeSet::new();
        internal_vars.insert("x".to_string());

        replace_vars_for_unroll_in_expr(&mut expr, &iterator, 1, 3, &internal_vars);

        assert_eq!(
            expr,
            Expression::Value(SimpleExpr::Var("@unrolled_1_3_x".to_string()))
        );
    }

    #[test]
    fn test_replace_vars_for_unroll_in_expr_value_external_var() {
        let mut expr = Expression::Value(SimpleExpr::Var("y".to_string()));
        let iterator = "i".to_string();
        let internal_vars = BTreeSet::new();

        replace_vars_for_unroll_in_expr(&mut expr, &iterator, 0, 2, &internal_vars);

        // External variables should not be modified
        assert_eq!(expr, Expression::Value(SimpleExpr::Var("y".to_string())));
    }

    #[test]
    fn test_replace_vars_for_unroll_in_expr_array_access() {
        let mut expr = Expression::ArrayAccess {
            array: SimpleExpr::Var("arr".to_string()),
            index: Box::new(Expression::Value(SimpleExpr::Var("i".to_string()))),
        };
        let iterator = "i".to_string();
        let mut internal_vars = BTreeSet::new();
        internal_vars.insert("arr".to_string());

        replace_vars_for_unroll_in_expr(&mut expr, &iterator, 2, 7, &internal_vars);

        assert_eq!(
            expr,
            Expression::ArrayAccess {
                array: SimpleExpr::Var("@unrolled_2_7_arr".to_string()),
                index: Box::new(Expression::scalar(7)),
            }
        );
    }

    #[test]
    fn test_replace_vars_for_unroll_in_expr_binary() {
        let mut expr = Expression::Binary {
            left: Box::new(Expression::Value(SimpleExpr::Var("i".to_string()))),
            operation: crate::ir::HighLevelOperation::Add,
            right: Box::new(Expression::Value(SimpleExpr::Var("x".to_string()))),
        };
        let iterator = "i".to_string();
        let mut internal_vars = BTreeSet::new();
        internal_vars.insert("x".to_string());

        replace_vars_for_unroll_in_expr(&mut expr, &iterator, 0, 10, &internal_vars);

        assert_eq!(
            expr,
            Expression::Binary {
                left: Box::new(Expression::scalar(10)),
                operation: crate::ir::HighLevelOperation::Add,
                right: Box::new(Expression::Value(SimpleExpr::Var(
                    "@unrolled_0_10_x".to_string()
                ))),
            }
        );
    }

    #[test]
    fn test_replace_vars_for_unroll_in_expr_log2_ceil() {
        let mut expr = Expression::Log2Ceil {
            value: Box::new(Expression::Value(SimpleExpr::Var("i".to_string()))),
        };
        let iterator = "i".to_string();
        let internal_vars = BTreeSet::new();

        replace_vars_for_unroll_in_expr(&mut expr, &iterator, 3, 16, &internal_vars);

        assert_eq!(
            expr,
            Expression::Log2Ceil {
                value: Box::new(Expression::scalar(16)),
            }
        );
    }

    #[test]
    fn test_replace_vars_for_unroll_assignment() {
        let mut lines = vec![Line::Assignment(Assignment {
            var: "sum".to_string(),
            value: Expression::Binary {
                left: Box::new(Expression::Value(SimpleExpr::Var("sum".to_string()))),
                operation: crate::ir::HighLevelOperation::Add,
                right: Box::new(Expression::Value(SimpleExpr::Var("i".to_string()))),
            },
        })];
        let iterator = "i".to_string();
        let mut internal_vars = BTreeSet::new();
        internal_vars.insert("sum".to_string());

        replace_vars_for_unroll(&mut lines, &iterator, 1, 5, &internal_vars);

        assert_eq!(
            lines,
            vec![Line::Assignment(Assignment {
                var: "@unrolled_1_5_sum".to_string(),
                value: Expression::Binary {
                    left: Box::new(Expression::Value(SimpleExpr::Var(
                        "@unrolled_1_5_sum".to_string()
                    ))),
                    operation: crate::ir::HighLevelOperation::Add,
                    right: Box::new(Expression::scalar(5)),
                },
            })]
        );
    }

    #[test]
    fn test_replace_vars_for_unroll_function_call() {
        let mut lines = vec![Line::FunctionCall(FunctionCall {
            function_name: "test_func".to_string(),
            args: vec![Expression::Value(SimpleExpr::Var("i".to_string()))],
            return_data: vec!["result".to_string()],
        })];
        let iterator = "i".to_string();
        let mut internal_vars = BTreeSet::new();
        internal_vars.insert("result".to_string());

        replace_vars_for_unroll(&mut lines, &iterator, 2, 8, &internal_vars);

        assert_eq!(
            lines,
            vec![Line::FunctionCall(FunctionCall {
                function_name: "test_func".to_string(),
                args: vec![Expression::scalar(8)],
                return_data: vec!["@unrolled_2_8_result".to_string()],
            })]
        );
    }

    #[test]
    fn test_replace_vars_for_unroll_if_condition() {
        let mut lines = vec![Line::IfCondition(IfCondition {
            condition: lang::Boolean::Equal {
                left: Expression::Value(SimpleExpr::Var("i".to_string())),
                right: Expression::scalar(5),
            },
            then_branch: vec![Line::Assignment(Assignment {
                var: "x".to_string(),
                value: Expression::scalar(1),
            })],
            else_branch: vec![],
        })];
        let iterator = "i".to_string();
        let mut internal_vars = BTreeSet::new();
        internal_vars.insert("x".to_string());

        replace_vars_for_unroll(&mut lines, &iterator, 0, 3, &internal_vars);

        assert_eq!(
            lines,
            vec![Line::IfCondition(IfCondition {
                condition: lang::Boolean::Equal {
                    left: Expression::scalar(3),
                    right: Expression::scalar(5),
                },
                then_branch: vec![Line::Assignment(Assignment {
                    var: "@unrolled_0_3_x".to_string(),
                    value: Expression::scalar(1),
                })],
                else_branch: vec![],
            })]
        );
    }

    #[test]
    fn test_replace_vars_for_unroll_for_loop() {
        let mut lines = vec![Line::ForLoop(lang::ForLoop {
            iterator: "j".to_string(),
            start: Expression::Value(SimpleExpr::Var("i".to_string())),
            end: Expression::scalar(10),
            body: vec![Line::Assignment(Assignment {
                var: "total".to_string(),
                value: Expression::Value(SimpleExpr::Var("j".to_string())),
            })],
            rev: false,
            unroll: false,
        })];
        let iterator = "i".to_string();
        let mut internal_vars = BTreeSet::new();
        internal_vars.insert("j".to_string());
        internal_vars.insert("total".to_string());

        replace_vars_for_unroll(&mut lines, &iterator, 1, 7, &internal_vars);

        assert_eq!(
            lines,
            vec![Line::ForLoop(lang::ForLoop {
                iterator: "@unrolled_1_7_j".to_string(),
                start: Expression::scalar(7),
                end: Expression::scalar(10),
                body: vec![Line::Assignment(Assignment {
                    var: "@unrolled_1_7_total".to_string(),
                    value: Expression::Value(SimpleExpr::Var("@unrolled_1_7_j".to_string())),
                })],
                rev: false,
                unroll: false,
            })]
        );
    }

    #[test]
    fn test_replace_vars_for_unroll_match() {
        let mut lines = vec![Line::Match(lang::Match {
            value: Expression::Value(SimpleExpr::Var("i".to_string())),
            arms: vec![
                (
                    0,
                    vec![Line::Assignment(Assignment {
                        var: "a".to_string(),
                        value: Expression::scalar(1),
                    })],
                ),
                (
                    1,
                    vec![Line::Assignment(Assignment {
                        var: "b".to_string(),
                        value: Expression::scalar(2),
                    })],
                ),
            ],
        })];
        let iterator = "i".to_string();
        let mut internal_vars = BTreeSet::new();
        internal_vars.insert("a".to_string());
        internal_vars.insert("b".to_string());

        replace_vars_for_unroll(&mut lines, &iterator, 3, 4, &internal_vars);

        assert_eq!(
            lines,
            vec![Line::Match(lang::Match {
                value: Expression::scalar(4),
                arms: vec![
                    (
                        0,
                        vec![Line::Assignment(Assignment {
                            var: "@unrolled_3_4_a".to_string(),
                            value: Expression::scalar(1),
                        })]
                    ),
                    (
                        1,
                        vec![Line::Assignment(Assignment {
                            var: "@unrolled_3_4_b".to_string(),
                            value: Expression::scalar(2),
                        })]
                    ),
                ],
            })]
        );
    }

    #[test]
    fn test_replace_vars_for_unroll_assert() {
        let mut lines = vec![Line::Assert(Assert {
            condition: lang::Boolean::Different {
                left: Expression::Value(SimpleExpr::Var("i".to_string())),
                right: Expression::Value(SimpleExpr::Var("x".to_string())),
            },
        })];
        let iterator = "i".to_string();
        let mut internal_vars = BTreeSet::new();
        internal_vars.insert("x".to_string());

        replace_vars_for_unroll(&mut lines, &iterator, 0, 6, &internal_vars);

        assert_eq!(
            lines,
            vec![Line::Assert(Assert {
                condition: lang::Boolean::Different {
                    left: Expression::scalar(6),
                    right: Expression::Value(SimpleExpr::Var("@unrolled_0_6_x".to_string())),
                }
            })]
        );
    }

    #[test]
    fn test_replace_vars_for_unroll_malloc() {
        let mut lines = vec![Line::MAlloc(MAlloc {
            var: "ptr".to_string(),
            size: Expression::Value(SimpleExpr::Var("i".to_string())),
            vectorized: false,
            vectorized_len: Expression::scalar(1),
        })];
        let iterator = "i".to_string();
        let mut internal_vars = BTreeSet::new();
        internal_vars.insert("ptr".to_string());

        replace_vars_for_unroll(&mut lines, &iterator, 1, 64, &internal_vars);

        assert_eq!(
            lines,
            vec![Line::MAlloc(MAlloc {
                var: "@unrolled_1_64_ptr".to_string(),
                size: Expression::scalar(64),
                vectorized: false,
                vectorized_len: Expression::scalar(1),
            })]
        );
    }

    #[test]
    fn test_replace_vars_for_unroll_decompose_bits() {
        let mut lines = vec![Line::DecomposeBits(DecomposeBits {
            var: "bits".to_string(),
            to_decompose: vec![Expression::Value(SimpleExpr::Var("i".to_string()))],
        })];
        let iterator = "i".to_string();
        let mut internal_vars = BTreeSet::new();
        internal_vars.insert("bits".to_string());

        replace_vars_for_unroll(&mut lines, &iterator, 2, 255, &internal_vars);

        assert_eq!(
            lines,
            vec![Line::DecomposeBits(DecomposeBits {
                var: "@unrolled_2_255_bits".to_string(),
                to_decompose: vec![Expression::scalar(255)],
            })]
        );
    }

    #[test]
    fn test_replace_vars_for_unroll_counter_hint() {
        let mut lines = vec![Line::CounterHint(CounterHint {
            var: "counter".to_string(),
        })];
        let iterator = "i".to_string();
        let mut internal_vars = BTreeSet::new();
        internal_vars.insert("counter".to_string());

        replace_vars_for_unroll(&mut lines, &iterator, 0, 1, &internal_vars);

        assert_eq!(
            lines,
            vec![Line::CounterHint(CounterHint {
                var: "@unrolled_0_1_counter".to_string(),
            })]
        );
    }

    #[test]
    fn test_replace_vars_for_unroll_print() {
        let mut lines = vec![Line::Print(Print {
            line_info: "debug".to_string(),
            content: vec![Expression::Value(SimpleExpr::Var("i".to_string()))],
        })];
        let iterator = "i".to_string();
        let internal_vars = BTreeSet::new();

        replace_vars_for_unroll(&mut lines, &iterator, 5, 42, &internal_vars);

        assert_eq!(
            lines,
            vec![Line::Print(Print {
                line_info: "debug (unrolled 5 42)".to_string(),
                content: vec![Expression::scalar(42)],
            })]
        );
    }

    #[test]
    fn test_replace_vars_for_unroll_array_assign() {
        let mut lines = vec![Line::ArrayAssign(ArrayAssign {
            array: SimpleExpr::Var("arr".to_string()),
            index: Expression::Value(SimpleExpr::Var("i".to_string())),
            value: Expression::Value(SimpleExpr::Var("val".to_string())),
        })];
        let iterator = "i".to_string();
        let mut internal_vars = BTreeSet::new();
        internal_vars.insert("arr".to_string());
        internal_vars.insert("val".to_string());

        replace_vars_for_unroll(&mut lines, &iterator, 1, 12, &internal_vars);

        assert_eq!(
            lines,
            vec![Line::ArrayAssign(ArrayAssign {
                array: SimpleExpr::Var("@unrolled_1_12_arr".to_string()),
                index: Expression::scalar(12),
                value: Expression::Value(SimpleExpr::Var("@unrolled_1_12_val".to_string())),
            })]
        );
    }

    #[test]
    fn test_replace_vars_for_unroll_function_ret() {
        let mut lines = vec![Line::FunctionRet(FunctionRet {
            return_data: vec![Expression::Value(SimpleExpr::Var("i".to_string()))],
        })];
        let iterator = "i".to_string();
        let internal_vars = BTreeSet::new();

        replace_vars_for_unroll(&mut lines, &iterator, 0, 100, &internal_vars);

        assert_eq!(
            lines,
            vec![Line::FunctionRet(FunctionRet {
                return_data: vec![Expression::scalar(100)],
            })]
        );
    }

    #[test]
    fn test_replace_vars_for_unroll_precompile() {
        let mut lines = vec![Line::Precompile(PrecompileStmt {
            precompile: crate::precompiles::PRECOMPILES[0].clone(),
            args: vec![Expression::Value(SimpleExpr::Var("i".to_string()))],
        })];
        let iterator = "i".to_string();
        let internal_vars = BTreeSet::new();

        replace_vars_for_unroll(&mut lines, &iterator, 3, 25, &internal_vars);

        assert_eq!(
            lines,
            vec![Line::Precompile(PrecompileStmt {
                precompile: crate::precompiles::PRECOMPILES[0].clone(),
                args: vec![Expression::scalar(25)],
            })]
        );
    }

    #[test]
    fn test_replace_vars_for_unroll_no_op_lines() {
        let mut lines = vec![
            Line::Break(Break),
            Line::Panic(Panic),
            Line::LocationReport(LocationReport { location: 42 }),
        ];
        let iterator = "i".to_string();
        let internal_vars = BTreeSet::new();

        let expected = lines.clone();
        replace_vars_for_unroll(&mut lines, &iterator, 0, 1, &internal_vars);

        assert_eq!(lines, expected); // Should remain unchanged
    }
}
