//! If condition statement implementation.

use crate::{
    F,
    ir::{
        unroll::{replace_vars_for_unroll, replace_vars_for_unroll_in_expr},
        utilities::replace_vars_by_const_in_expr,
    },
    lang::{
        ast::types::Boolean, find_variable_usage, get_function_called,
        replace_vars_by_const_in_lines, values::Var,
    },
    traits::IndentedDisplay,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::{Display, Formatter},
};

use super::traits::StatementAnalysis;

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

impl StatementAnalysis for IfCondition {
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

    fn get_function_calls(&self, function_calls: &mut Vec<String>) {
        get_function_called(&self.then_branch, function_calls);
        get_function_called(&self.else_branch, function_calls);
    }

    fn find_internal_vars(&self) -> (BTreeSet<Var>, BTreeSet<Var>) {
        let mut internal_vars = BTreeSet::new();
        let mut external_vars = BTreeSet::new();

        // Helper function to extract vars from boolean condition
        let add_condition_vars =
            |condition: &Boolean, external_vars: &mut BTreeSet<Var>| match condition {
                Boolean::Equal { left, right } | Boolean::Different { left, right } => {
                    for var in crate::ir::utilities::vars_in_expression(left) {
                        external_vars.insert(var);
                    }
                    for var in crate::ir::utilities::vars_in_expression(right) {
                        external_vars.insert(var);
                    }
                }
            };

        // Add condition variables as external
        add_condition_vars(&self.condition, &mut external_vars);

        // Recursively find variables in then/else branches
        let (then_internal, then_external) = find_variable_usage(&self.then_branch);
        let (else_internal, else_external) = find_variable_usage(&self.else_branch);

        // Variables defined in either branch are internal to the if statement
        internal_vars.extend(then_internal.union(&else_internal).cloned());

        // External variables from branches (excluding already internal ones)
        external_vars.extend(
            then_external
                .union(&else_external)
                .filter(|v| !internal_vars.contains(*v))
                .cloned(),
        );

        (internal_vars, external_vars)
    }
}

// Legacy trait compatibility
