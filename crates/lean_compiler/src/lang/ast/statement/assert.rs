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

use super::traits::{ReplaceVarsForUnroll, ReplaceVarsWithConst};

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

impl ReplaceVarsForUnroll for Assert {
    fn replace_vars_for_unroll(
        &mut self,
        iterator: &Var,
        unroll_index: usize,
        iterator_value: usize,
        internal_vars: &BTreeSet<Var>,
    ) {
        match &mut self.condition {
            Boolean::Equal { left, right } | Boolean::Different { left, right } => {
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
}

impl ReplaceVarsWithConst for Assert {
    fn replace_vars_with_const(&mut self, map: &BTreeMap<Var, F>) {
        match &mut self.condition {
            Boolean::Equal { left, right } | Boolean::Different { left, right } => {
                crate::ir::utilities::replace_vars_by_const_in_expr(left, map);
                crate::ir::utilities::replace_vars_by_const_in_expr(right, map);
            }
        }
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
