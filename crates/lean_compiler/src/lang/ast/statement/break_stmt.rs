//! Break statement implementation.

use crate::traits::IndentedDisplay;
use std::fmt::{Display, Formatter};

use super::traits::StatementAnalysis;

/// Break statement for loop control.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Break;

impl Display for Break {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "break")
    }
}

impl IndentedDisplay for Break {}

// Break uses all default implementations from StatementAnalysis
impl StatementAnalysis for Break {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_break_display() {
        let break_stmt = Break;
        assert_eq!(break_stmt.to_string(), "break");
    }

    #[test]
    fn test_break_indented_display() {
        let break_stmt = Break;
        assert_eq!(break_stmt.to_string_with_indent(1), "    break");
    }
}
