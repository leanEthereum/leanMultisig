use std::fmt;

use crate::{
    lang::{Var, boolean::Boolean, expression::Expression},
    precompiles::Precompile,
};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Line {
    Assignment {
        var: Var,
        value: Expression,
    },
    ArrayAssign {
        // array[index] = value
        array: Var,
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
        res: Vec<Var>,
    },
    Break,
    Panic,
    // Hints:
    Print {
        line_info: String,
        content: Vec<Expression>,
    },
    MAlloc {
        var: Var,
        size: Expression,
        vectorized: bool,
    },
    DecomposeBits {
        var: Var, // a pointer to 31 field elements, containing the bits of "to_decompose"
        to_decompose: Expression,
    },
}

impl Line {
    pub(crate) fn to_string_with_indent(&self, indent: usize) -> String {
        let spaces = "    ".repeat(indent);
        let line_str = match self {
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
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ");
                let return_data_str = return_data
                    .iter()
                    .map(ToString::to_string)
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
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("return {return_data_str}")
            }
            Self::Precompile {
                precompile,
                args,
                res: return_data,
            } => {
                format!(
                    "{} = {}({})",
                    return_data
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>()
                        .join(", "),
                    precompile.name,
                    args.iter()
                        .map(ToString::to_string)
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
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("print({content_str})")
            }
            Self::MAlloc {
                var,
                size,
                vectorized,
            } => {
                if *vectorized {
                    format!("{var} = malloc_vectorized({size})")
                } else {
                    format!("{var} = malloc({size})")
                }
            }
            Self::DecomposeBits { var, to_decompose } => {
                format!("{var} = decompose_bits({to_decompose})")
            }
            Self::Break => "break".to_string(),
            Self::Panic => "panic".to_string(),
        };
        format!("{spaces}{line_str}")
    }
}

impl fmt::Display for Line {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_string_with_indent(0))
    }
}
