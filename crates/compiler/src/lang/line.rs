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
            Line::Assignment { var, value } => {
                format!("{} = {}", var.to_string(), value.to_string())
            }
            Line::ArrayAssign {
                array,
                index,
                value,
            } => {
                format!(
                    "{}[{}] = {}",
                    array.to_string(),
                    index.to_string(),
                    value.to_string()
                )
            }
            Line::Assert(condition) => format!("assert {}", condition.to_string()),
            Line::IfCondition {
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
                    format!(
                        "if {} {{\n{}\n{}}}",
                        condition.to_string(),
                        then_str,
                        spaces
                    )
                } else {
                    format!(
                        "if {} {{\n{}\n{}}} else {{\n{}\n{}}}",
                        condition.to_string(),
                        then_str,
                        spaces,
                        else_str,
                        spaces
                    )
                }
            }
            Line::ForLoop {
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
                    iterator.to_string(),
                    start.to_string(),
                    if *rev { "rev " } else { "" },
                    end.to_string(),
                    if *unroll { "unroll " } else { "" },
                    body_str,
                    spaces
                )
            }
            Line::FunctionCall {
                function_name,
                args,
                return_data,
            } => {
                let args_str = args
                    .iter()
                    .map(|arg| arg.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                let return_data_str = return_data
                    .iter()
                    .map(|var| var.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");

                if return_data.is_empty() {
                    format!("{}({})", function_name, args_str)
                } else {
                    format!("{} = {}({})", return_data_str, function_name, args_str)
                }
            }
            Line::FunctionRet { return_data } => {
                let return_data_str = return_data
                    .iter()
                    .map(|arg| arg.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("return {}", return_data_str)
            }
            Line::Precompile {
                precompile,
                args,
                res: return_data,
            } => {
                format!(
                    "{} = {}({})",
                    return_data
                        .iter()
                        .map(|var| var.to_string())
                        .collect::<Vec<_>>()
                        .join(", "),
                    precompile.name.to_string(),
                    args.iter()
                        .map(|arg| arg.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            Line::Print {
                line_info: _,
                content,
            } => {
                let content_str = content
                    .iter()
                    .map(|c| c.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("print({})", content_str)
            }
            Line::MAlloc {
                var,
                size,
                vectorized,
            } => {
                if *vectorized {
                    format!(
                        "{} = malloc_vectorized({})",
                        var.to_string(),
                        size.to_string()
                    )
                } else {
                    format!("{} = malloc({})", var.to_string(), size.to_string())
                }
            }
            Line::DecomposeBits { var, to_decompose } => {
                format!(
                    "{} = decompose_bits({})",
                    var.to_string(),
                    to_decompose.to_string()
                )
            }
            Line::Break => "break".to_string(),
            Line::Panic => "panic".to_string(),
        };
        format!("{}{}", spaces, line_str)
    }
}

impl fmt::Display for Line {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_string_with_indent(0))
    }
}
