//! Match statement implementation.

use crate::{
    F,
    ir::unroll::{replace_vars_for_unroll, replace_vars_for_unroll_in_expr},
    lang::{expr::Expression, values::Var},
    traits::IndentedDisplay,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::{Display, Formatter},
};

use super::traits::StatementAnalysis;

/// Pattern matching statement.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Match {
    /// Expression to match against
    pub value: Expression,
    /// Match arms with patterns and bodies
    pub arms: Vec<(usize, Vec<super::Line>)>,
}

impl Display for Match {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let arms_str = self
            .arms
            .iter()
            .map(|(const_expr, body)| {
                let body_str = body
                    .iter()
                    .map(|line| line.to_string_with_indent(1))
                    .collect::<Vec<_>>()
                    .join("\n");
                format!("{const_expr} => {{\n{body_str}\n}}")
            })
            .collect::<Vec<_>>()
            .join("\n");
        write!(f, "match {} {{\n{arms_str}\n}}", self.value)
    }
}

impl IndentedDisplay for Match {
    fn to_string_with_indent(&self, indent: usize) -> String {
        let spaces = "    ".repeat(indent);
        let arms_str = self
            .arms
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
        format!("{spaces}match {} {{\n{arms_str}\n{spaces}}}", self.value)
    }
}

impl StatementAnalysis for Match {
    fn replace_vars_for_unroll(
        &mut self,
        iterator: &Var,
        unroll_index: usize,
        iterator_value: usize,
        internal_vars: &BTreeSet<Var>,
    ) {
        replace_vars_for_unroll_in_expr(
            &mut self.value,
            iterator,
            unroll_index,
            iterator_value,
            internal_vars,
        );
        for (_, body) in &mut self.arms {
            replace_vars_for_unroll(body, iterator, unroll_index, iterator_value, internal_vars);
        }
    }

    fn replace_vars_with_const(&mut self, map: &BTreeMap<Var, F>) {
        crate::ir::utilities::replace_vars_by_const_in_expr(&mut self.value, map);
        for (_, body) in &mut self.arms {
            for line in body {
                line.replace_vars_with_const(map);
            }
        }
    }

    fn get_function_calls(&self, function_calls: &mut Vec<String>) {
        crate::ir::utilities::get_function_calls_in_expr(&self.value, function_calls);
        for (_, body) in &self.arms {
            for line in body {
                line.get_function_calls(function_calls);
            }
        }
    }

    fn find_internal_vars(&self) -> (BTreeSet<Var>, BTreeSet<Var>) {
        let mut internal_vars = BTreeSet::new();
        let mut external_vars = BTreeSet::new();

        let (value_internal, value_external) =
            crate::ir::utilities::find_internal_vars_in_expr(&self.value);
        internal_vars.extend(value_internal);
        external_vars.extend(value_external);

        for (_, body) in &self.arms {
            for line in body {
                let (line_internal, line_external) = line.find_internal_vars();
                internal_vars.extend(line_internal);
                external_vars.extend(line_external);
            }
        }

        (internal_vars, external_vars)
    }
}
