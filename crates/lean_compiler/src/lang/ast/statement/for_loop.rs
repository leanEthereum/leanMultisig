//! For loop statement implementation.

use crate::{
    F,
    ir::{
        replace_vars_by_const_in_lines, unroll::replace_vars_for_unroll,
        utilities::replace_vars_by_const_in_expr,
    },
    lang::{expr::Expression, values::Var},
    traits::IndentedDisplay,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::{Display, Formatter},
};

use super::traits::{ReplaceVarsForUnroll, ReplaceVarsWithConst};

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

impl ReplaceVarsForUnroll for ForLoop {
    fn replace_vars_for_unroll(
        &mut self,
        iterator: &Var,
        unroll_index: usize,
        iterator_value: usize,
        internal_vars: &BTreeSet<Var>,
    ) {
        assert!(self.iterator != *iterator);
        self.iterator = format!(
            "@unrolled_{unroll_index}_{iterator_value}_{}",
            self.iterator
        );
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
        replace_vars_for_unroll(
            &mut self.body,
            iterator,
            unroll_index,
            iterator_value,
            internal_vars,
        );
    }
}

impl ReplaceVarsWithConst for ForLoop {
    fn replace_vars_with_const(&mut self, map: &BTreeMap<Var, F>) {
        replace_vars_by_const_in_expr(&mut self.start, map);
        replace_vars_by_const_in_expr(&mut self.end, map);
        replace_vars_by_const_in_lines(&mut self.body, map);
    }
}
