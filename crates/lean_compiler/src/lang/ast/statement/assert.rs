//! Assert statement implementation.

use crate::{
    F,
    lang::{ast::types::Boolean, values::Var},
    traits::IndentedDisplay,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::{Display, Formatter},
};

use super::traits::StatementAnalysis;

/// Assert statement for runtime checks.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Assert {
    /// Boolean condition to assert
    pub condition: Boolean,
}

impl Display for Assert {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "assert {}", self.condition)
    }
}

impl IndentedDisplay for Assert {}

impl StatementAnalysis for Assert {
    fn replace_vars_for_unroll(
        &mut self,
        iterator: &Var,
        unroll_index: usize,
        iterator_value: usize,
        internal_vars: &BTreeSet<Var>,
    ) {
        match &mut self.condition {
            Boolean::Equal { left, right } => {
                crate::ir::unroll::replace_vars_for_unroll_in_expr(
                    left,
                    iterator,
                    unroll_index,
                    iterator_value,
                    internal_vars,
                );
                crate::ir::unroll::replace_vars_for_unroll_in_expr(
                    right,
                    iterator,
                    unroll_index,
                    iterator_value,
                    internal_vars,
                );
            }
            Boolean::Different { left, right } => {
                crate::ir::unroll::replace_vars_for_unroll_in_expr(
                    left,
                    iterator,
                    unroll_index,
                    iterator_value,
                    internal_vars,
                );
                crate::ir::unroll::replace_vars_for_unroll_in_expr(
                    right,
                    iterator,
                    unroll_index,
                    iterator_value,
                    internal_vars,
                );
            }
        }
    }

    fn replace_vars_with_const(&mut self, map: &BTreeMap<Var, F>) {
        match &mut self.condition {
            Boolean::Equal { left, right } => {
                crate::ir::utilities::replace_vars_by_const_in_expr(left, map);
                crate::ir::utilities::replace_vars_by_const_in_expr(right, map);
            }
            Boolean::Different { left, right } => {
                crate::ir::utilities::replace_vars_by_const_in_expr(left, map);
                crate::ir::utilities::replace_vars_by_const_in_expr(right, map);
            }
        }
    }

    fn get_function_calls(&self, function_calls: &mut Vec<String>) {
        match &self.condition {
            Boolean::Equal { left, right } => {
                crate::ir::utilities::get_function_calls_in_expr(left, function_calls);
                crate::ir::utilities::get_function_calls_in_expr(right, function_calls);
            }
            Boolean::Different { left, right } => {
                crate::ir::utilities::get_function_calls_in_expr(left, function_calls);
                crate::ir::utilities::get_function_calls_in_expr(right, function_calls);
            }
        }
    }

    fn find_internal_vars(&self) -> (BTreeSet<Var>, BTreeSet<Var>) {
        let mut internal_vars = BTreeSet::new();
        let mut external_vars = BTreeSet::new();

        match &self.condition {
            Boolean::Equal { left, right } => {
                let (left_internal, left_external) =
                    crate::ir::utilities::find_internal_vars_in_expr(left);
                let (right_internal, right_external) =
                    crate::ir::utilities::find_internal_vars_in_expr(right);
                internal_vars.extend(left_internal);
                internal_vars.extend(right_internal);
                external_vars.extend(left_external);
                external_vars.extend(right_external);
            }
            Boolean::Different { left, right } => {
                let (left_internal, left_external) =
                    crate::ir::utilities::find_internal_vars_in_expr(left);
                let (right_internal, right_external) =
                    crate::ir::utilities::find_internal_vars_in_expr(right);
                internal_vars.extend(left_internal);
                internal_vars.extend(right_internal);
                external_vars.extend(left_external);
                external_vars.extend(right_external);
            }
        }

        (internal_vars, external_vars)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::{
        ast::types::Boolean,
        expr::{Expression, SimpleExpr},
    };

    #[test]
    fn test_assert_display() {
        let assert_stmt = Assert {
            condition: Boolean::Equal {
                left: Expression::Value(SimpleExpr::Var("x".to_string())),
                right: Expression::scalar(10),
            },
        };
        assert_eq!(assert_stmt.to_string(), "assert x == 10");
    }

    #[test]
    fn test_assert_different_display() {
        let assert_stmt = Assert {
            condition: Boolean::Different {
                left: Expression::scalar(5),
                right: Expression::scalar(0),
            },
        };
        assert_eq!(assert_stmt.to_string(), "assert 5 != 0");
    }
}
