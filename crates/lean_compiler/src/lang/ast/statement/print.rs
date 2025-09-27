//! Print statement implementation.

use crate::{lang::expr::Expression, traits::IndentedDisplay};
use std::fmt::{Display, Formatter};

/// Debug print statement.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Print {
    /// Line information for debugging
    pub line_info: String,
    /// Expressions to print
    pub content: Vec<Expression>,
}

impl Display for Print {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let content_str = self
            .content
            .iter()
            .map(|c| format!("{c}"))
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "print({content_str})")
    }
}

impl IndentedDisplay for Print {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::expr::{Expression, SimpleExpr};

    #[test]
    fn test_print_display() {
        let print = Print {
            line_info: "debug".to_string(),
            content: vec![
                Expression::scalar(42),
                Expression::Value(SimpleExpr::Var("x".to_string())),
            ],
        };
        assert_eq!(print.to_string(), "print(42, x)");
    }

    #[test]
    fn test_print_empty() {
        let print = Print {
            line_info: "empty".to_string(),
            content: vec![],
        };
        assert_eq!(print.to_string(), "print()");
    }

    #[test]
    fn test_print_single_value() {
        let print = Print {
            line_info: "single".to_string(),
            content: vec![Expression::scalar(100)],
        };
        assert_eq!(print.to_string(), "print(100)");
    }
}
