//! Panic statement implementation.

use crate::traits::IndentedDisplay;
use std::fmt::{Display, Formatter};

use super::traits::StatementAnalysis;

/// Unconditional program termination.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Panic;

impl Display for Panic {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "panic")
    }
}

impl IndentedDisplay for Panic {}

impl StatementAnalysis for Panic {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_panic_display() {
        let panic_stmt = Panic;
        assert_eq!(panic_stmt.to_string(), "panic");
    }

    #[test]
    fn test_panic_indented_display() {
        let panic_stmt = Panic;
        assert_eq!(panic_stmt.to_string_with_indent(2), "        panic");
    }
}
