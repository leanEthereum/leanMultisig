//! Statement types for the AST.

use lean_vm::SourceLineNumber;
use std::fmt::{Display, Formatter};

use crate::lang::values::Var;
use crate::precompiles::Precompile;

use super::{expr::{Expression, SimpleExpr}, types::Boolean};

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
                    "for {} in {}{}..{} {}{{\n{}\n{}}}",
                    iterator,
                    start,
                    if *rev { "rev " } else { "" },
                    end,
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