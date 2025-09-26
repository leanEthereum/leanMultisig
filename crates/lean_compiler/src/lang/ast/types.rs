//! Basic type definitions for the AST.

use std::fmt::{Display, Formatter};

use super::expr::Expression;

/// Boolean condition for assertions and control flow.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Boolean {
    /// Equality comparison.
    Equal { left: Expression, right: Expression },
    /// Inequality comparison.
    Different { left: Expression, right: Expression },
}

impl Display for Boolean {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Equal { left, right } => {
                write!(f, "{left} == {right}")
            }
            Self::Different { left, right } => {
                write!(f, "{left} != {right}")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::SimpleExpr;

    #[test]
    fn test_boolean_equal_display() {
        let equal = Boolean::Equal {
            left: Expression::scalar(5),
            right: Expression::scalar(10),
        };
        assert_eq!(equal.to_string(), "5 == 10");
    }

    #[test]
    fn test_boolean_different_display() {
        let different = Boolean::Different {
            left: Expression::Value(SimpleExpr::Var("x".to_string())),
            right: Expression::scalar(0),
        };
        assert_eq!(different.to_string(), "x != 0");
    }
}