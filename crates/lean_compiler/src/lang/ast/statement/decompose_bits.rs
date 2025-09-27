//! Bit decomposition statement implementation.

use crate::{
    lang::{expr::Expression, values::Var},
    traits::IndentedDisplay,
};
use std::fmt::{Display, Formatter};

/// Bit decomposition statement for field elements.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DecomposeBits {
    /// Variable to store the decomposed bits
    pub var: Var,
    /// Expressions to decompose into bits
    pub to_decompose: Vec<Expression>,
}

impl Display for DecomposeBits {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} = decompose_bits({})",
            self.var,
            self.to_decompose
                .iter()
                .map(|expr| expr.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

impl IndentedDisplay for DecomposeBits {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::expr::{Expression, SimpleExpr};

    #[test]
    fn test_decompose_bits_display() {
        let decompose = DecomposeBits {
            var: "bits".to_string(),
            to_decompose: vec![
                Expression::scalar(255),
                Expression::Value(SimpleExpr::Var("y".to_string())),
            ],
        };
        assert_eq!(decompose.to_string(), "bits = decompose_bits(255, y)");
    }

    #[test]
    fn test_decompose_bits_single_value() {
        let decompose = DecomposeBits {
            var: "single_bits".to_string(),
            to_decompose: vec![Expression::scalar(42)],
        };
        assert_eq!(decompose.to_string(), "single_bits = decompose_bits(42)");
    }

    #[test]
    fn test_decompose_bits_empty() {
        let decompose = DecomposeBits {
            var: "empty_bits".to_string(),
            to_decompose: vec![],
        };
        assert_eq!(decompose.to_string(), "empty_bits = decompose_bits()");
    }
}
