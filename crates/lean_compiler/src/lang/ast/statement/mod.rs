//! Statement types and implementations.

pub mod array_assign;
pub mod assert;
pub mod assignment;
pub mod break_stmt;
pub mod counter_hint;
pub mod decompose_bits;
pub mod for_loop;
pub mod function_call;
pub mod function_ret;
pub mod if_condition;
pub mod location_report;
pub mod malloc;
pub mod match_stmt;
pub mod panic;
pub mod precompile;
pub mod print;
pub mod traits;

use crate::{F, lang::Var, traits::IndentedDisplay};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::{Display, Formatter},
};
use traits::StatementAnalysis;

pub use array_assign::ArrayAssign;
pub use assert::Assert;
pub use assignment::Assignment;
pub use break_stmt::Break;
pub use counter_hint::CounterHint;
pub use decompose_bits::DecomposeBits;
pub use for_loop::ForLoop;
pub use function_call::FunctionCall;
pub use function_ret::FunctionRet;
pub use if_condition::IfCondition;
pub use location_report::LocationReport;
pub use malloc::MAlloc;
pub use match_stmt::Match;
pub use panic::Panic;
pub use precompile::PrecompileStmt;
pub use print::Print;

/// A statement in the Lean language.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Line {
    /// Pattern matching with computed jumps
    Match(Match),
    /// Variable assignment with expressions
    Assignment(Assignment),
    /// Array element assignment
    ArrayAssign(ArrayAssign),
    /// Runtime assertion checks
    Assert(Assert),
    /// Conditional branching (if-else)
    IfCondition(IfCondition),
    /// For loop iteration
    ForLoop(ForLoop),
    /// Function invocation with argument passing
    FunctionCall(FunctionCall),
    /// Function return with values
    FunctionRet(FunctionRet),
    /// Precompiled cryptographic operations
    Precompile(PrecompileStmt),
    /// Break statement for loop control
    Break(Break),
    /// Unconditional program termination
    Panic(Panic),
    /// Debug print statement
    Print(Print),
    /// Memory allocation
    MAlloc(MAlloc),
    /// Bit decomposition for field elements
    DecomposeBits(DecomposeBits),
    /// Counter value hint for loops
    CounterHint(CounterHint),
    /// Source location tracking for debugging
    LocationReport(LocationReport),
}

impl Display for Line {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Line::Match(stmt) => write!(f, "{}", stmt),
            Line::Assignment(stmt) => write!(f, "{}", stmt),
            Line::ArrayAssign(stmt) => write!(f, "{}", stmt),
            Line::Assert(stmt) => write!(f, "{}", stmt),
            Line::IfCondition(stmt) => write!(f, "{}", stmt),
            Line::ForLoop(stmt) => write!(f, "{}", stmt),
            Line::FunctionCall(stmt) => write!(f, "{}", stmt),
            Line::FunctionRet(stmt) => write!(f, "{}", stmt),
            Line::Precompile(stmt) => write!(f, "{}", stmt),
            Line::Break(stmt) => write!(f, "{}", stmt),
            Line::Panic(stmt) => write!(f, "{}", stmt),
            Line::Print(stmt) => write!(f, "{}", stmt),
            Line::MAlloc(stmt) => write!(f, "{}", stmt),
            Line::DecomposeBits(stmt) => write!(f, "{}", stmt),
            Line::CounterHint(stmt) => write!(f, "{}", stmt),
            Line::LocationReport(stmt) => write!(f, "{}", stmt),
        }
    }
}

impl IndentedDisplay for Line {
    fn to_string_with_indent(&self, indent: usize) -> String {
        match self {
            Line::Match(stmt) => stmt.to_string_with_indent(indent),
            Line::Assignment(stmt) => stmt.to_string_with_indent(indent),
            Line::ArrayAssign(stmt) => stmt.to_string_with_indent(indent),
            Line::Assert(stmt) => stmt.to_string_with_indent(indent),
            Line::IfCondition(stmt) => stmt.to_string_with_indent(indent),
            Line::ForLoop(stmt) => stmt.to_string_with_indent(indent),
            Line::FunctionCall(stmt) => stmt.to_string_with_indent(indent),
            Line::FunctionRet(stmt) => stmt.to_string_with_indent(indent),
            Line::Precompile(stmt) => stmt.to_string_with_indent(indent),
            Line::Break(stmt) => stmt.to_string_with_indent(indent),
            Line::Panic(stmt) => stmt.to_string_with_indent(indent),
            Line::Print(stmt) => stmt.to_string_with_indent(indent),
            Line::MAlloc(stmt) => stmt.to_string_with_indent(indent),
            Line::DecomposeBits(stmt) => stmt.to_string_with_indent(indent),
            Line::CounterHint(stmt) => stmt.to_string_with_indent(indent),
            Line::LocationReport(stmt) => stmt.to_string_with_indent(indent),
        }
    }
}

impl StatementAnalysis for Line {
    fn replace_vars_for_unroll(
        &mut self,
        iterator: &crate::lang::values::Var,
        unroll_index: usize,
        iterator_value: usize,
        internal_vars: &BTreeSet<crate::lang::values::Var>,
    ) {
        match self {
            Line::Match(stmt) => {
                stmt.replace_vars_for_unroll(iterator, unroll_index, iterator_value, internal_vars)
            }
            Line::Assignment(stmt) => {
                stmt.replace_vars_for_unroll(iterator, unroll_index, iterator_value, internal_vars)
            }
            Line::ArrayAssign(stmt) => {
                stmt.replace_vars_for_unroll(iterator, unroll_index, iterator_value, internal_vars)
            }
            Line::Assert(stmt) => {
                stmt.replace_vars_for_unroll(iterator, unroll_index, iterator_value, internal_vars)
            }
            Line::IfCondition(stmt) => {
                stmt.replace_vars_for_unroll(iterator, unroll_index, iterator_value, internal_vars)
            }
            Line::ForLoop(stmt) => {
                stmt.replace_vars_for_unroll(iterator, unroll_index, iterator_value, internal_vars)
            }
            Line::FunctionCall(stmt) => {
                stmt.replace_vars_for_unroll(iterator, unroll_index, iterator_value, internal_vars)
            }
            Line::FunctionRet(stmt) => {
                stmt.replace_vars_for_unroll(iterator, unroll_index, iterator_value, internal_vars)
            }
            Line::Precompile(stmt) => {
                stmt.replace_vars_for_unroll(iterator, unroll_index, iterator_value, internal_vars)
            }
            Line::Break(stmt) => {
                stmt.replace_vars_for_unroll(iterator, unroll_index, iterator_value, internal_vars)
            }
            Line::Panic(stmt) => {
                stmt.replace_vars_for_unroll(iterator, unroll_index, iterator_value, internal_vars)
            }
            Line::Print(stmt) => {
                stmt.replace_vars_for_unroll(iterator, unroll_index, iterator_value, internal_vars)
            }
            Line::MAlloc(stmt) => {
                stmt.replace_vars_for_unroll(iterator, unroll_index, iterator_value, internal_vars)
            }
            Line::DecomposeBits(stmt) => {
                stmt.replace_vars_for_unroll(iterator, unroll_index, iterator_value, internal_vars)
            }
            Line::CounterHint(stmt) => {
                stmt.replace_vars_for_unroll(iterator, unroll_index, iterator_value, internal_vars)
            }
            Line::LocationReport(stmt) => {
                stmt.replace_vars_for_unroll(iterator, unroll_index, iterator_value, internal_vars)
            }
        }
    }

    fn replace_vars_with_const(&mut self, map: &BTreeMap<crate::lang::values::Var, F>) {
        match self {
            Line::Match(stmt) => stmt.replace_vars_with_const(map),
            Line::Assignment(stmt) => stmt.replace_vars_with_const(map),
            Line::ArrayAssign(stmt) => stmt.replace_vars_with_const(map),
            Line::Assert(stmt) => stmt.replace_vars_with_const(map),
            Line::IfCondition(stmt) => stmt.replace_vars_with_const(map),
            Line::ForLoop(stmt) => stmt.replace_vars_with_const(map),
            Line::FunctionCall(stmt) => stmt.replace_vars_with_const(map),
            Line::FunctionRet(stmt) => stmt.replace_vars_with_const(map),
            Line::Precompile(stmt) => stmt.replace_vars_with_const(map),
            Line::Break(stmt) => stmt.replace_vars_with_const(map),
            Line::Panic(stmt) => stmt.replace_vars_with_const(map),
            Line::Print(stmt) => stmt.replace_vars_with_const(map),
            Line::MAlloc(stmt) => stmt.replace_vars_with_const(map),
            Line::DecomposeBits(stmt) => stmt.replace_vars_with_const(map),
            Line::CounterHint(stmt) => stmt.replace_vars_with_const(map),
            Line::LocationReport(stmt) => stmt.replace_vars_with_const(map),
        }
    }

    fn get_function_calls(&self, function_calls: &mut Vec<String>) {
        match self {
            Line::Match(stmt) => stmt.get_function_calls(function_calls),
            Line::Assignment(stmt) => stmt.get_function_calls(function_calls),
            Line::ArrayAssign(stmt) => stmt.get_function_calls(function_calls),
            Line::Assert(stmt) => stmt.get_function_calls(function_calls),
            Line::IfCondition(stmt) => stmt.get_function_calls(function_calls),
            Line::ForLoop(stmt) => stmt.get_function_calls(function_calls),
            Line::FunctionCall(stmt) => stmt.get_function_calls(function_calls),
            Line::FunctionRet(stmt) => stmt.get_function_calls(function_calls),
            Line::Precompile(stmt) => stmt.get_function_calls(function_calls),
            Line::Break(stmt) => stmt.get_function_calls(function_calls),
            Line::Panic(stmt) => stmt.get_function_calls(function_calls),
            Line::Print(stmt) => stmt.get_function_calls(function_calls),
            Line::MAlloc(stmt) => stmt.get_function_calls(function_calls),
            Line::DecomposeBits(stmt) => stmt.get_function_calls(function_calls),
            Line::CounterHint(stmt) => stmt.get_function_calls(function_calls),
            Line::LocationReport(stmt) => stmt.get_function_calls(function_calls),
        }
    }

    fn find_internal_vars(
        &self,
    ) -> (
        BTreeSet<crate::lang::values::Var>,
        BTreeSet<crate::lang::values::Var>,
    ) {
        match self {
            Line::Match(stmt) => stmt.find_internal_vars(),
            Line::Assignment(stmt) => stmt.find_internal_vars(),
            Line::ArrayAssign(stmt) => stmt.find_internal_vars(),
            Line::Assert(stmt) => stmt.find_internal_vars(),
            Line::IfCondition(stmt) => stmt.find_internal_vars(),
            Line::ForLoop(stmt) => stmt.find_internal_vars(),
            Line::FunctionCall(stmt) => stmt.find_internal_vars(),
            Line::FunctionRet(stmt) => stmt.find_internal_vars(),
            Line::Precompile(stmt) => stmt.find_internal_vars(),
            Line::Break(stmt) => stmt.find_internal_vars(),
            Line::Panic(stmt) => stmt.find_internal_vars(),
            Line::Print(stmt) => stmt.find_internal_vars(),
            Line::MAlloc(stmt) => stmt.find_internal_vars(),
            Line::DecomposeBits(stmt) => stmt.find_internal_vars(),
            Line::CounterHint(stmt) => stmt.find_internal_vars(),
            Line::LocationReport(stmt) => stmt.find_internal_vars(),
        }
    }
}

/// Replace variables with constants in a line sequence.
pub fn replace_vars_by_const_in_lines(lines: &mut [Line], map: &BTreeMap<Var, F>) {
    for line in lines {
        line.replace_vars_with_const(map);
    }
}

/// Extract function calls from line sequence.
pub fn get_function_called(lines: &[Line], function_called: &mut Vec<String>) {
    for line in lines {
        line.get_function_calls(function_called);
    }
}

/// Returns (internal_vars, external_vars) for a sequence of lines.
pub fn find_variable_usage(lines: &[Line]) -> (BTreeSet<Var>, BTreeSet<Var>) {
    let mut internal_vars = BTreeSet::new();
    let mut external_vars = BTreeSet::new();

    for line in lines {
        let (line_internal, line_external) = line.find_internal_vars();
        internal_vars.extend(line_internal);
        external_vars.extend(
            line_external
                .into_iter()
                .filter(|v| !internal_vars.contains(v)),
        );
    }

    (internal_vars, external_vars)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::{
        ast::types::Boolean,
        expr::{Expression, SimpleExpr},
    };
    use p3_field::PrimeCharacteristicRing;

    #[test]
    fn test_line_assignment_display() {
        let line = Line::Assignment(Assignment {
            var: "x".to_string(),
            value: Expression::scalar(42),
        });
        assert_eq!(line.to_string(), "x = 42");
    }

    #[test]
    fn test_line_panic_display() {
        let line = Line::Panic(Panic);
        assert_eq!(line.to_string(), "panic");
    }

    #[test]
    fn test_line_break_display() {
        let line = Line::Break(Break);
        assert_eq!(line.to_string(), "break");
    }

    #[test]
    fn test_line_assert_display() {
        let line = Line::Assert(Assert {
            condition: Boolean::Equal {
                left: Expression::Value(SimpleExpr::Var("x".to_string())),
                right: Expression::scalar(10),
            },
        });
        assert_eq!(line.to_string(), "assert x == 10");
    }

    #[test]
    fn test_line_indented_display() {
        let line = Line::Assignment(Assignment {
            var: "y".to_string(),
            value: Expression::scalar(100),
        });
        assert_eq!(line.to_string_with_indent(2), "        y = 100");
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
        let lines = vec![Line::FunctionCall(FunctionCall {
            function_name: "test_func".to_string(),
            args: vec![],
            return_data: vec![],
        })];
        let mut function_called = Vec::new();

        get_function_called(&lines, &mut function_called);

        assert_eq!(function_called, vec!["test_func".to_string()]);
    }

    #[test]
    fn test_get_function_called_multiple_calls() {
        let lines = vec![
            Line::FunctionCall(FunctionCall {
                function_name: "func1".to_string(),
                args: vec![],
                return_data: vec![],
            }),
            Line::Assignment(Assignment {
                var: "x".to_string(),
                value: Expression::scalar(42),
            }),
            Line::FunctionCall(FunctionCall {
                function_name: "func2".to_string(),
                args: vec![],
                return_data: vec![],
            }),
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
        let lines = vec![Line::IfCondition(IfCondition {
            condition: Boolean::Equal {
                left: Expression::scalar(1),
                right: Expression::scalar(1),
            },
            then_branch: vec![Line::FunctionCall(FunctionCall {
                function_name: "then_func".to_string(),
                args: vec![],
                return_data: vec![],
            })],
            else_branch: vec![Line::FunctionCall(FunctionCall {
                function_name: "else_func".to_string(),
                args: vec![],
                return_data: vec![],
            })],
        })];
        let mut function_called = Vec::new();

        get_function_called(&lines, &mut function_called);

        assert_eq!(
            function_called,
            vec!["then_func".to_string(), "else_func".to_string()]
        );
    }

    #[test]
    fn test_get_function_called_for_loop() {
        let lines = vec![Line::ForLoop(ForLoop {
            iterator: "i".to_string(),
            start: Expression::scalar(0),
            end: Expression::scalar(10),
            body: vec![Line::FunctionCall(FunctionCall {
                function_name: "loop_func".to_string(),
                args: vec![],
                return_data: vec![],
            })],
            rev: false,
            unroll: false,
        })];
        let mut function_called = Vec::new();

        get_function_called(&lines, &mut function_called);

        assert_eq!(function_called, vec!["loop_func".to_string()]);
    }

    #[test]
    fn test_get_function_called_match() {
        let lines = vec![Line::Match(Match {
            value: Expression::scalar(1),
            arms: vec![
                (
                    0,
                    vec![Line::FunctionCall(FunctionCall {
                        function_name: "arm0_func".to_string(),
                        args: vec![],
                        return_data: vec![],
                    })],
                ),
                (
                    1,
                    vec![Line::FunctionCall(FunctionCall {
                        function_name: "arm1_func".to_string(),
                        args: vec![],
                        return_data: vec![],
                    })],
                ),
            ],
        })];
        let mut function_called = Vec::new();

        get_function_called(&lines, &mut function_called);

        assert_eq!(
            function_called,
            vec!["arm0_func".to_string(), "arm1_func".to_string()]
        );
    }

    #[test]
    fn test_replace_vars_by_const_in_lines_assignment() {
        let mut lines = vec![Line::Assignment(Assignment {
            var: "y".to_string(),
            value: Expression::Value(SimpleExpr::Var("x".to_string())),
        })];
        let mut map = BTreeMap::new();
        map.insert("x".to_string(), crate::F::from_usize(42));

        replace_vars_by_const_in_lines(&mut lines, &map);

        assert_eq!(
            lines,
            vec![Line::Assignment(Assignment {
                var: "y".to_string(),
                value: Expression::scalar(42),
            })]
        );
    }

    #[test]
    fn test_replace_vars_by_const_in_lines_function_call() {
        let mut lines = vec![Line::FunctionCall(FunctionCall {
            function_name: "test".to_string(),
            args: vec![Expression::Value(SimpleExpr::Var("x".to_string()))],
            return_data: vec!["result".to_string()],
        })];
        let mut map = BTreeMap::new();
        map.insert("x".to_string(), crate::F::from_usize(100));

        replace_vars_by_const_in_lines(&mut lines, &map);

        assert_eq!(
            lines,
            vec![Line::FunctionCall(FunctionCall {
                function_name: "test".to_string(),
                args: vec![Expression::scalar(100)],
                return_data: vec!["result".to_string()],
            })]
        );
    }

    #[test]
    fn test_replace_vars_by_const_in_lines_if_condition() {
        let mut lines = vec![Line::IfCondition(IfCondition {
            condition: Boolean::Equal {
                left: Expression::Value(SimpleExpr::Var("x".to_string())),
                right: Expression::scalar(10),
            },
            then_branch: vec![Line::Assignment(Assignment {
                var: "y".to_string(),
                value: Expression::Value(SimpleExpr::Var("x".to_string())),
            })],
            else_branch: vec![],
        })];
        let mut map = BTreeMap::new();
        map.insert("x".to_string(), crate::F::from_usize(5));

        replace_vars_by_const_in_lines(&mut lines, &map);

        assert_eq!(
            lines,
            vec![Line::IfCondition(IfCondition {
                condition: Boolean::Equal {
                    left: Expression::scalar(5),
                    right: Expression::scalar(10),
                },
                then_branch: vec![Line::Assignment(Assignment {
                    var: "y".to_string(),
                    value: Expression::scalar(5),
                })],
                else_branch: vec![],
            })]
        );
    }

    #[test]
    fn test_find_variable_usage_empty() {
        let lines: Vec<Line> = vec![];
        let (internal, external) = find_variable_usage(&lines);

        assert!(internal.is_empty());
        assert!(external.is_empty());
    }

    #[test]
    fn test_find_variable_usage_assignment() {
        let lines = vec![Line::Assignment(Assignment {
            var: "x".to_string(),
            value: Expression::scalar(42),
        })];
        let (internal, external) = find_variable_usage(&lines);

        assert_eq!(internal, BTreeSet::from(["x".to_string()]));
        assert!(external.is_empty());
    }

    #[test]
    fn test_find_variable_usage_assignment_with_external_var() {
        let lines = vec![Line::Assignment(Assignment {
            var: "x".to_string(),
            value: Expression::Value(SimpleExpr::Var("y".to_string())),
        })];
        let (internal, external) = find_variable_usage(&lines);

        assert_eq!(internal, BTreeSet::from(["x".to_string()]));
        assert_eq!(external, BTreeSet::from(["y".to_string()]));
    }

    #[test]
    fn test_find_variable_usage_function_call() {
        let lines = vec![Line::FunctionCall(FunctionCall {
            function_name: "test".to_string(),
            args: vec![Expression::Value(SimpleExpr::Var("input".to_string()))],
            return_data: vec!["output".to_string()],
        })];
        let (internal, external) = find_variable_usage(&lines);

        assert_eq!(internal, BTreeSet::from(["output".to_string()]));
        assert_eq!(external, BTreeSet::from(["input".to_string()]));
    }

    #[test]
    fn test_find_variable_usage_if_condition() {
        let lines = vec![Line::IfCondition(IfCondition {
            condition: Boolean::Equal {
                left: Expression::Value(SimpleExpr::Var("a".to_string())),
                right: Expression::scalar(10),
            },
            then_branch: vec![Line::Assignment(Assignment {
                var: "b".to_string(),
                value: Expression::scalar(1),
            })],
            else_branch: vec![Line::Assignment(Assignment {
                var: "c".to_string(),
                value: Expression::scalar(2),
            })],
        })];
        let (internal, external) = find_variable_usage(&lines);

        assert_eq!(internal, BTreeSet::from(["b".to_string(), "c".to_string()]));
        assert_eq!(external, BTreeSet::from(["a".to_string()]));
    }

    #[test]
    fn test_find_variable_usage_for_loop() {
        let lines = vec![Line::ForLoop(ForLoop {
            iterator: "i".to_string(),
            start: Expression::scalar(0),
            end: Expression::Value(SimpleExpr::Var("n".to_string())),
            body: vec![Line::Assignment(Assignment {
                var: "sum".to_string(),
                value: Expression::Binary {
                    left: Box::new(Expression::Value(SimpleExpr::Var("sum".to_string()))),
                    operation: crate::ir::HighLevelOperation::Add,
                    right: Box::new(Expression::Value(SimpleExpr::Var("i".to_string()))),
                },
            })],
            rev: false,
            unroll: false,
        })];
        let (internal, external) = find_variable_usage(&lines);

        assert_eq!(
            internal,
            BTreeSet::from(["i".to_string(), "sum".to_string()])
        );
        assert_eq!(external, BTreeSet::from(["n".to_string()]));
    }

    #[test]
    fn test_find_variable_usage_match() {
        let lines = vec![Line::Match(Match {
            value: Expression::Value(SimpleExpr::Var("x".to_string())),
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
        let (internal, external) = find_variable_usage(&lines);

        assert_eq!(internal, BTreeSet::from(["a".to_string(), "b".to_string()]));
        assert_eq!(external, BTreeSet::from(["x".to_string()]));
    }

    #[test]
    fn test_find_variable_usage_malloc() {
        let lines = vec![Line::MAlloc(MAlloc {
            var: "ptr".to_string(),
            size: Expression::Value(SimpleExpr::Var("size".to_string())),
            vectorized: false,
            vectorized_len: Expression::zero(),
        })];
        let (internal, external) = find_variable_usage(&lines);

        assert_eq!(internal, BTreeSet::from(["ptr".to_string()]));
        assert_eq!(external, BTreeSet::from(["size".to_string()]));
    }

    #[test]
    fn test_find_variable_usage_decompose_bits() {
        let lines = vec![Line::DecomposeBits(DecomposeBits {
            var: "bits".to_string(),
            to_decompose: vec![Expression::Value(SimpleExpr::Var("value".to_string()))],
        })];
        let (internal, external) = find_variable_usage(&lines);

        assert_eq!(internal, BTreeSet::from(["bits".to_string()]));
        assert_eq!(external, BTreeSet::from(["value".to_string()]));
    }

    #[test]
    fn test_find_variable_usage_counter_hint() {
        let lines = vec![Line::CounterHint(CounterHint {
            var: "counter".to_string(),
        })];
        let (internal, external) = find_variable_usage(&lines);

        assert_eq!(internal, BTreeSet::from(["counter".to_string()]));
        assert!(external.is_empty());
    }

    #[test]
    fn test_find_variable_usage_assert() {
        let lines = vec![Line::Assert(Assert {
            condition: Boolean::Different {
                left: Expression::Value(SimpleExpr::Var("x".to_string())),
                right: Expression::Value(SimpleExpr::Var("y".to_string())),
            },
        })];
        let (internal, external) = find_variable_usage(&lines);

        assert!(internal.is_empty());
        assert_eq!(external, BTreeSet::from(["x".to_string(), "y".to_string()]));
    }

    #[test]
    fn test_find_variable_usage_function_ret() {
        let lines = vec![Line::FunctionRet(FunctionRet {
            return_data: vec![Expression::Value(SimpleExpr::Var("result".to_string()))],
        })];
        let (internal, external) = find_variable_usage(&lines);

        assert!(internal.is_empty());
        assert_eq!(external, BTreeSet::from(["result".to_string()]));
    }

    #[test]
    fn test_find_variable_usage_precompile() {
        let lines = vec![Line::Precompile(PrecompileStmt {
            precompile: crate::precompiles::PRECOMPILES[0].clone(),
            args: vec![Expression::Value(SimpleExpr::Var("input".to_string()))],
        })];
        let (internal, external) = find_variable_usage(&lines);

        assert!(internal.is_empty());
        assert_eq!(external, BTreeSet::from(["input".to_string()]));
    }

    #[test]
    fn test_find_variable_usage_print() {
        let lines = vec![Line::Print(Print {
            line_info: "debug".to_string(),
            content: vec![Expression::Value(SimpleExpr::Var("debug_var".to_string()))],
        })];
        let (internal, external) = find_variable_usage(&lines);

        assert!(internal.is_empty());
        assert_eq!(external, BTreeSet::from(["debug_var".to_string()]));
    }

    #[test]
    fn test_find_variable_usage_array_assign() {
        let lines = vec![Line::ArrayAssign(ArrayAssign {
            array: SimpleExpr::Var("arr".to_string()),
            index: Expression::Value(SimpleExpr::Var("idx".to_string())),
            value: Expression::Value(SimpleExpr::Var("val".to_string())),
        })];
        let (internal, external) = find_variable_usage(&lines);

        assert!(internal.is_empty());
        assert_eq!(
            external,
            BTreeSet::from(["arr".to_string(), "idx".to_string(), "val".to_string()])
        );
    }
}
