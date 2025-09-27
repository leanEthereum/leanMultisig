//! Assignment statement implementation.

use crate::{
    F,
    lang::{expr::Expression, values::Var},
    traits::IndentedDisplay,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::{Display, Formatter},
};

use super::traits::StatementAnalysis;

/// Variable assignment statement.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Assignment {
    /// Target variable for assignment
    pub var: Var,
    /// Expression value to assign
    pub value: Expression,
}

impl Display for Assignment {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} = {}", self.var, self.value)
    }
}

impl IndentedDisplay for Assignment {}

impl StatementAnalysis for Assignment {
    fn replace_vars_for_unroll(
        &mut self,
        iterator: &Var,
        unroll_index: usize,
        iterator_value: usize,
        internal_vars: &BTreeSet<Var>,
    ) {
        assert!(self.var != *iterator, "Weird");
        self.var = format!("@unrolled_{unroll_index}_{iterator_value}_{}", self.var);
        crate::ir::unroll::replace_vars_for_unroll_in_expr(
            &mut self.value,
            iterator,
            unroll_index,
            iterator_value,
            internal_vars,
        );
    }

    fn replace_vars_with_const(&mut self, map: &BTreeMap<Var, F>) {
        assert!(
            !map.contains_key(&self.var),
            "Variable {} is a constant",
            self.var
        );
        crate::ir::utilities::replace_vars_by_const_in_expr(&mut self.value, map);
    }

    fn find_internal_vars(&self) -> (BTreeSet<Var>, BTreeSet<Var>) {
        let mut internal_vars = BTreeSet::new();
        let mut external_vars = BTreeSet::new();

        // The assigned variable is internal
        internal_vars.insert(self.var.clone());

        // Variables used in the expression are external (unless they're already internal)
        for var in crate::ir::utilities::vars_in_expression(&self.value) {
            if !internal_vars.contains(&var) {
                external_vars.insert(var);
            }
        }

        (internal_vars, external_vars)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::expr::Expression;

    #[test]
    fn test_assignment_display() {
        let assignment = Assignment {
            var: "x".to_string(),
            value: Expression::scalar(42),
        };
        assert_eq!(assignment.to_string(), "x = 42");
    }

    #[test]
    fn test_assignment_indented_display() {
        let assignment = Assignment {
            var: "y".to_string(),
            value: Expression::scalar(10),
        };
        assert_eq!(assignment.to_string_with_indent(1), "    y = 10");
    }
}
