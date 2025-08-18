use std::fmt;

use crate::lang::expression::Expression;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Boolean {
    Equal { left: Expression, right: Expression },
    Different { left: Expression, right: Expression },
}

impl fmt::Display for Boolean {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Equal { left, right } => write!(f, "{left} == {right}"),
            Self::Different { left, right } => write!(f, "{left} != {right}"),
        }
    }
}
