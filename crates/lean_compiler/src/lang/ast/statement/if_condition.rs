//! If condition statement implementation.

use crate::{
    F,
    ir::{
        replace_vars_by_const_in_lines,
        unroll::{replace_vars_for_unroll, replace_vars_for_unroll_in_expr},
        utilities::replace_vars_by_const_in_expr,
    },
    lang::{ast::types::Boolean, values::Var},
    traits::IndentedDisplay,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::{Display, Formatter},
};

use super::traits::{ReplaceVarsForUnroll, ReplaceVarsWithConst};

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
        let then_str = self
            .then_branch
            .iter()
            .map(|line| line.to_string_with_indent(1))
            .collect::<Vec<_>>()
            .join("\n");

        let else_str = self
            .else_branch
            .iter()
            .map(|line| line.to_string_with_indent(1))
            .collect::<Vec<_>>()
            .join("\n");

        if self.else_branch.is_empty() {
            write!(f, "if {} {{\n{then_str}\n}}", self.condition)
        } else {
            write!(
                f,
                "if {} {{\n{then_str}\n}} else {{\n{else_str}\n}}",
                self.condition
            )
        }
    }
}

impl IndentedDisplay for IfCondition {
    fn to_string_with_indent(&self, indent: usize) -> String {
        let spaces = "    ".repeat(indent);
        let then_str = self
            .then_branch
            .iter()
            .map(|line| line.to_string_with_indent(indent + 1))
            .collect::<Vec<_>>()
            .join("\n");

        let else_str = self
            .else_branch
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

impl ReplaceVarsForUnroll for IfCondition {
    fn replace_vars_for_unroll(
        &mut self,
        iterator: &Var,
        unroll_index: usize,
        iterator_value: usize,
        internal_vars: &BTreeSet<Var>,
    ) {
        match &mut self.condition {
            crate::lang::ast::types::Boolean::Equal { left, right }
            | crate::lang::ast::types::Boolean::Different { left, right } => {
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
        }
        replace_vars_for_unroll(
            &mut self.then_branch,
            iterator,
            unroll_index,
            iterator_value,
            internal_vars,
        );
        replace_vars_for_unroll(
            &mut self.else_branch,
            iterator,
            unroll_index,
            iterator_value,
            internal_vars,
        );
    }
}

impl ReplaceVarsWithConst for IfCondition {
    fn replace_vars_with_const(&mut self, map: &BTreeMap<Var, F>) {
        match &mut self.condition {
            crate::lang::ast::types::Boolean::Equal { left, right }
            | crate::lang::ast::types::Boolean::Different { left, right } => {
                replace_vars_by_const_in_expr(left, map);
                replace_vars_by_const_in_expr(right, map);
            }
        }
        replace_vars_by_const_in_lines(&mut self.then_branch, map);
        replace_vars_by_const_in_lines(&mut self.else_branch, map);
    }
}
