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