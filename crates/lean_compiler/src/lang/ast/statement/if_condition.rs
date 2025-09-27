//! If condition statement implementation.

use crate::{
    lang::ast::types::Boolean,
    traits::IndentedDisplay,
};
use std::fmt::{Display, Formatter};

/// Conditional branching statement.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct IfCondition {
    /// Boolean condition to evaluate
    pub condition: Boolean,
    /// Statements to execute if condition is true
    pub then_branch: Vec<super::Line>,
    /// Statements to execute if condition is false
    pub else_branch: Vec<super::Line>,
}

impl Display for IfCondition {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let then_str = self.then_branch
            .iter()
            .map(|line| line.to_string_with_indent(1))
            .collect::<Vec<_>>()
            .join("\n");

        let else_str = self.else_branch
            .iter()
            .map(|line| line.to_string_with_indent(1))
            .collect::<Vec<_>>()
            .join("\n");

        if self.else_branch.is_empty() {
            write!(f, "if {} {{\n{then_str}\n}}", self.condition)
        } else {
            write!(f, "if {} {{\n{then_str}\n}} else {{\n{else_str}\n}}", self.condition)
        }
    }
}

impl IndentedDisplay for IfCondition {
    fn to_string_with_indent(&self, indent: usize) -> String {
        let spaces = "    ".repeat(indent);
        let then_str = self.then_branch
            .iter()
            .map(|line| line.to_string_with_indent(indent + 1))
            .collect::<Vec<_>>()
            .join("\n");

        let else_str = self.else_branch
            .iter()
            .map(|line| line.to_string_with_indent(indent + 1))
            .collect::<Vec<_>>()
            .join("\n");

        if self.else_branch.is_empty() {
            format!("{spaces}if {} {{\n{then_str}\n{spaces}}}", self.condition)
        } else {
            format!(
                "{spaces}if {} {{\n{then_str}\n{spaces}}} else {{\n{else_str}\n{spaces}}}",
                self.condition
            )
        }
    }
}