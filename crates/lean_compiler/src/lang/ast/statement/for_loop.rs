//! For loop statement implementation.

use crate::{
    F,
    ir::unroll::replace_vars_for_unroll,
    lang::{expr::Expression, replace_vars_by_const_in_lines, values::Var},
    traits::IndentedDisplay,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::{Display, Formatter},
};

use super::traits::StatementAnalysis;

/// For loop statement.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ForLoop {
    /// Iterator variable name
    pub iterator: Var,
    /// Start expression for the loop
    pub start: Expression,
    /// End expression for the loop
    pub end: Expression,
    /// Loop body statements
    pub body: Vec<super::Line>,
    /// Whether to iterate in reverse order
    pub rev: bool,
    /// Whether to unroll the loop
    pub unroll: bool,
}

impl Display for ForLoop {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let body_str = self
            .body
            .iter()
            .map(|line| line.to_string_with_indent(1))
            .collect::<Vec<_>>()
            .join("\n");
        write!(
            f,
            "for {} in {}..{} {}{}{{\n{}\n}}",
            self.iterator,
            self.start,
            self.end,
            if self.rev { "rev " } else { "" },
            if self.unroll { "unroll " } else { "" },
            body_str,
        )
    }
}

impl IndentedDisplay for ForLoop {
    fn to_string_with_indent(&self, indent: usize) -> String {
        let spaces = "    ".repeat(indent);
        let body_str = self
            .body
            .iter()
            .map(|line| line.to_string_with_indent(indent + 1))
            .collect::<Vec<_>>()
            .join("\n");
        format!(
            "{}for {} in {}..{} {}{}{{\n{}\n{}}}",
            spaces,
            self.iterator,
            self.start,
            self.end,
            if self.rev { "rev " } else { "" },
            if self.unroll { "unroll " } else { "" },
            body_str,
            spaces
        )
    }
}

impl StatementAnalysis for ForLoop {
    fn replace_vars_for_unroll(
        &mut self,
        iterator: &Var,
        unroll_index: usize,
        iterator_value: usize,
        internal_vars: &BTreeSet<Var>,
    ) {
        // Replace variables in start and end expressions
        crate::ir::unroll::replace_vars_for_unroll_in_expr(
            &mut self.start,
            iterator,
            unroll_index,
            iterator_value,
            internal_vars,
        );
        crate::ir::unroll::replace_vars_for_unroll_in_expr(
            &mut self.end,
            iterator,
            unroll_index,
            iterator_value,
            internal_vars,
        );

        // Rename the iterator variable if it's internal
        if internal_vars.contains(&self.iterator) {
            self.iterator = format!(
                "@unrolled_{unroll_index}_{iterator_value}_{}",
                self.iterator
            );
        }

        // Process the loop body
        replace_vars_for_unroll(
            &mut self.body,
            iterator,
            unroll_index,
            iterator_value,
            internal_vars,
        );
    }

    fn replace_vars_with_const(&mut self, map: &BTreeMap<Var, F>) {
        crate::ir::utilities::replace_vars_by_const_in_expr(&mut self.start, map);
        crate::ir::utilities::replace_vars_by_const_in_expr(&mut self.end, map);
        replace_vars_by_const_in_lines(&mut self.body, map);
    }

    fn get_function_calls(&self, function_calls: &mut Vec<String>) {
        crate::ir::utilities::get_function_calls_in_expr(&self.start, function_calls);
        crate::ir::utilities::get_function_calls_in_expr(&self.end, function_calls);
        for line in &self.body {
            line.get_function_calls(function_calls);
        }
    }

    fn find_internal_vars(&self) -> (BTreeSet<Var>, BTreeSet<Var>) {
        let mut internal_vars = BTreeSet::new();
        let mut external_vars = BTreeSet::new();

        // The iterator variable is internal to the loop
        internal_vars.insert(self.iterator.clone());

        let (start_internal, start_external) =
            crate::ir::utilities::find_internal_vars_in_expr(&self.start);
        internal_vars.extend(start_internal);
        external_vars.extend(start_external);

        let (end_internal, end_external) =
            crate::ir::utilities::find_internal_vars_in_expr(&self.end);
        internal_vars.extend(end_internal);
        external_vars.extend(end_external);

        for line in &self.body {
            let (line_internal, line_external) = line.find_internal_vars();
            internal_vars.extend(line_internal);
            external_vars.extend(line_external);
        }

        (internal_vars, external_vars)
    }
}
