//! Assignment statement implementation.

use crate::{
    lang::{expr::Expression, values::Var},
    traits::IndentedDisplay,
};
use std::fmt::{Display, Formatter};

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