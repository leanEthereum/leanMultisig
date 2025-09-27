//! Assert statement implementation.

use crate::{lang::ast::types::Boolean, traits::IndentedDisplay};
use std::fmt::{Display, Formatter};

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
