//! Statement types for the AST.

use lean_vm::SourceLineNumber;
use std::fmt::{Display, Formatter};

use crate::lang::values::Var;
use crate::precompiles::Precompile;

use super::{
    expr::{Expression, SimpleExpr},
    types::Boolean,
};

/// A statement in the Lean language.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Line {
    Match {
        value: Expression,
        arms: Vec<(usize, Vec<Self>)>,
    },
    Assignment {
        var: Var,
        value: Expression,
    },
    ArrayAssign {
        array: SimpleExpr,
        index: Expression,
        value: Expression,
    },
    Assert(Boolean),
    IfCondition {
        condition: Boolean,
        then_branch: Vec<Self>,
        else_branch: Vec<Self>,
    },
    ForLoop {
        iterator: Var,
        start: Expression,
        end: Expression,
        body: Vec<Self>,
        rev: bool,
        unroll: bool,
    },
    FunctionCall {
        function_name: String,
        args: Vec<Expression>,
        return_data: Vec<Var>,
    },
    FunctionRet {
        return_data: Vec<Expression>,
    },
    Precompile {
        precompile: Precompile,
        args: Vec<Expression>,
    },
    Break,
    Panic,
    Print {
        line_info: String,
        content: Vec<Expression>,
    },
    MAlloc {
        var: Var,
        size: Expression,
        vectorized: bool,
        vectorized_len: Expression,
    },
    DecomposeBits {
        var: Var,
        to_decompose: Vec<Expression>,
    },
    CounterHint {
        var: Var,
    },
    LocationReport {
        location: SourceLineNumber,
    },
}

impl Line {
    /// Converts the statement to a string with proper indentation.
    fn to_string_with_indent(&self, indent: usize) -> String {
        let spaces = "    ".repeat(indent);
        let line_str = match self {
            Self::LocationReport { .. } => Default::default(),
            Self::Match { value, arms } => {
                let arms_str = arms
                    .iter()
                    .map(|(const_expr, body)| {
                        let body_str = body
                            .iter()
                            .map(|line| line.to_string_with_indent(indent + 1))
                            .collect::<Vec<_>>()
                            .join("\n");
                        format!("{const_expr} => {{\n{body_str}\n{spaces}}}")
                    })
                    .collect::<Vec<_>>()
                    .join("\n");
                format!("match {value} {{\n{arms_str}\n{spaces}}}")
            }
            Self::Assignment { var, value } => {
                format!("{var} = {value}")
            }
            Self::ArrayAssign {
                array,
                index,
                value,
            } => {
                format!("{array}[{index}] = {value}")
            }
            Self::Assert(condition) => format!("assert {condition}"),
            Self::IfCondition {
                condition,
                then_branch,
                else_branch,
            } => {
                let then_str = then_branch
                    .iter()
                    .map(|line| line.to_string_with_indent(indent + 1))
                    .collect::<Vec<_>>()
                    .join("\n");

                let else_str = else_branch
                    .iter()
                    .map(|line| line.to_string_with_indent(indent + 1))
                    .collect::<Vec<_>>()
                    .join("\n");

                if else_branch.is_empty() {
                    format!("if {condition} {{\n{then_str}\n{spaces}}}")
                } else {
                    format!(
                        "if {condition} {{\n{then_str}\n{spaces}}} else {{\n{else_str}\n{spaces}}}"
                    )
                }
            }
            Self::CounterHint { var } => {
                format!("{var} = counter_hint({var})")
            }
            Self::ForLoop {
                iterator,
                start,
                end,
                body,
                rev,
                unroll,
            } => {
                let body_str = body
                    .iter()
                    .map(|line| line.to_string_with_indent(indent + 1))
                    .collect::<Vec<_>>()
                    .join("\n");
                format!(
                    "for {} in {}..{} {}{}{{\n{}\n{}}}",
                    iterator,
                    start,
                    end,
                    if *rev { "rev " } else { "" },
                    if *unroll { "unroll " } else { "" },
                    body_str,
                    spaces
                )
            }
            Self::FunctionCall {
                function_name,
                args,
                return_data,
            } => {
                let args_str = args
                    .iter()
                    .map(|arg| format!("{arg}"))
                    .collect::<Vec<_>>()
                    .join(", ");
                let return_data_str = return_data
                    .iter()
                    .map(|var| var.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");

                if return_data.is_empty() {
                    format!("{function_name}({args_str})")
                } else {
                    format!("{return_data_str} = {function_name}({args_str})")
                }
            }
            Self::FunctionRet { return_data } => {
                let return_data_str = return_data
                    .iter()
                    .map(|arg| format!("{arg}"))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("return {return_data_str}")
            }
            Self::Precompile { precompile, args } => {
                format!(
                    "{}({})",
                    precompile.name,
                    args.iter()
                        .map(|arg| format!("{arg}"))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            Self::Print {
                line_info: _,
                content,
            } => {
                let content_str = content
                    .iter()
                    .map(|c| format!("{c}"))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("print({content_str})")
            }
            Self::MAlloc {
                var,
                size,
                vectorized,
                vectorized_len,
            } => {
                if *vectorized {
                    format!("{var} = malloc_vec({size}, {vectorized_len})")
                } else {
                    format!("{var} = malloc({size})")
                }
            }
            Self::DecomposeBits { var, to_decompose } => {
                format!(
                    "{} = decompose_bits({})",
                    var,
                    to_decompose
                        .iter()
                        .map(|expr| expr.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            Self::Break => "break".to_string(),
            Self::Panic => "panic".to_string(),
        };
        format!("{spaces}{line_str}")
    }
}

impl Display for Line {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_string_with_indent(0))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_line_assignment_display() {
        let assignment = Line::Assignment {
            var: "x".to_string(),
            value: Expression::scalar(42),
        };
        assert_eq!(assignment.to_string(), "x = 42");
    }

    #[test]
    fn test_line_array_assign_display() {
        let array_assign = Line::ArrayAssign {
            array: SimpleExpr::Var("arr".to_string()),
            index: Expression::scalar(0),
            value: Expression::scalar(10),
        };
        assert_eq!(array_assign.to_string(), "arr[0] = 10");
    }

    #[test]
    fn test_line_break_panic_display() {
        assert_eq!(Line::Break.to_string(), "break");
        assert_eq!(Line::Panic.to_string(), "panic");
    }

    #[test]
    fn test_line_malloc_display() {
        let malloc = Line::MAlloc {
            var: "ptr".to_string(),
            size: Expression::scalar(100),
            vectorized: false,
            vectorized_len: Expression::scalar(1),
        };
        assert_eq!(malloc.to_string(), "ptr = malloc(100)");

        let malloc_vec = Line::MAlloc {
            var: "ptr".to_string(),
            size: Expression::scalar(100),
            vectorized: true,
            vectorized_len: Expression::scalar(8),
        };
        assert_eq!(malloc_vec.to_string(), "ptr = malloc_vec(100, 8)");
    }

    #[test]
    fn test_line_function_call_display() {
        let call = Line::FunctionCall {
            function_name: "test_fn".to_string(),
            args: vec![Expression::scalar(1), Expression::scalar(2)],
            return_data: vec!["result".to_string()],
        };
        assert_eq!(call.to_string(), "result = test_fn(1, 2)");

        let call_no_return = Line::FunctionCall {
            function_name: "void_fn".to_string(),
            args: vec![Expression::scalar(42)],
            return_data: vec![],
        };
        assert_eq!(call_no_return.to_string(), "void_fn(42)");
    }

    #[test]
    fn test_line_return_display() {
        let ret = Line::FunctionRet {
            return_data: vec![Expression::scalar(1), Expression::scalar(2)],
        };
        assert_eq!(ret.to_string(), "return 1, 2");
    }

    #[test]
    fn test_line_assert_display() {
        let assert_stmt = Line::Assert(Boolean::Equal {
            left: Expression::Value(SimpleExpr::Var("x".to_string())),
            right: Expression::scalar(10),
        });
        assert_eq!(assert_stmt.to_string(), "assert x == 10");
    }

    #[test]
    fn test_line_counter_hint_display() {
        let hint = Line::CounterHint {
            var: "counter".to_string(),
        };
        assert_eq!(hint.to_string(), "counter = counter_hint(counter)");
    }

    #[test]
    fn test_line_print_display() {
        let print = Line::Print {
            line_info: "debug".to_string(),
            content: vec![
                Expression::scalar(42),
                Expression::Value(SimpleExpr::Var("x".to_string())),
            ],
        };
        assert_eq!(print.to_string(), "print(42, x)");
    }

    #[test]
    fn test_line_decompose_bits_display() {
        let decompose = Line::DecomposeBits {
            var: "bits".to_string(),
            to_decompose: vec![
                Expression::scalar(255),
                Expression::Value(SimpleExpr::Var("y".to_string())),
            ],
        };
        assert_eq!(decompose.to_string(), "bits = decompose_bits(255, y)");
    }

    #[test]
    fn test_line_for_loop_display() {
        let for_loop = Line::ForLoop {
            iterator: "i".to_string(),
            start: Expression::scalar(0),
            end: Expression::scalar(10),
            body: vec![Line::Break],
            rev: false,
            unroll: false,
        };
        assert_eq!(for_loop.to_string(), "for i in 0..10 {\n    break\n}");

        let for_loop_rev_unroll = Line::ForLoop {
            iterator: "i".to_string(),
            start: Expression::scalar(0),
            end: Expression::scalar(5),
            body: vec![],
            rev: true,
            unroll: true,
        };
        assert_eq!(
            for_loop_rev_unroll.to_string(),
            "for i in 0..5 rev unroll {\n\n}"
        );
    }

    #[test]
    fn test_line_if_condition_display() {
        let if_simple = Line::IfCondition {
            condition: Boolean::Equal {
                left: Expression::Value(SimpleExpr::Var("x".to_string())),
                right: Expression::scalar(0),
            },
            then_branch: vec![Line::Panic],
            else_branch: vec![],
        };
        assert_eq!(if_simple.to_string(), "if x == 0 {\n    panic\n}");

        let if_else = Line::IfCondition {
            condition: Boolean::Different {
                left: Expression::scalar(1),
                right: Expression::scalar(2),
            },
            then_branch: vec![Line::Break],
            else_branch: vec![Line::Panic],
        };
        assert_eq!(
            if_else.to_string(),
            "if 1 != 2 {\n    break\n} else {\n    panic\n}"
        );
    }

    #[test]
    fn test_line_match_display() {
        let match_stmt = Line::Match {
            value: Expression::Value(SimpleExpr::Var("x".to_string())),
            arms: vec![(0, vec![Line::Break]), (1, vec![Line::Panic])],
        };
        assert_eq!(
            match_stmt.to_string(),
            "match x {\n0 => {\n    break\n}\n1 => {\n    panic\n}\n}"
        );
    }

    #[test]
    fn test_line_location_report_display() {
        let location = Line::LocationReport { location: 42 };
        assert_eq!(location.to_string(), "");
    }
}
