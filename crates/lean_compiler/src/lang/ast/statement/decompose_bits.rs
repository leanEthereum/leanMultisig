//! Bit decomposition statement implementation.

use crate::{
    F,
    lang::{expr::Expression, values::Var},
    traits::IndentedDisplay,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::{Display, Formatter},
};

use super::traits::{ReplaceVarsForUnroll, ReplaceVarsWithConst};

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

impl ReplaceVarsForUnroll for DecomposeBits {
    fn replace_vars_for_unroll(
        &mut self,
        iterator: &Var,
        unroll_index: usize,
        iterator_value: usize,
        internal_vars: &BTreeSet<Var>,
    ) {
        assert!(self.var != *iterator, "Weird");
        self.var = format!("@unrolled_{unroll_index}_{iterator_value}_{}", self.var);
        for expr in &mut self.to_decompose {
            crate::ir::unroll::replace_vars_for_unroll_in_expr(
                expr,
                iterator,
                unroll_index,
                iterator_value,
                internal_vars,
            );
        }
    }
}

impl ReplaceVarsWithConst for DecomposeBits {
    fn replace_vars_with_const(&mut self, map: &BTreeMap<Var, F>) {
        assert!(
            !map.contains_key(&self.var),
            "Variable {} is a constant",
            self.var
        );
        for expr in &mut self.to_decompose {
            crate::ir::utilities::replace_vars_by_const_in_expr(expr, map);
        }
    }
}

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
