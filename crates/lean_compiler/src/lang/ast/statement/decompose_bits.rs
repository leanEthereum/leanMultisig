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

use super::traits::StatementAnalysis;

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

impl StatementAnalysis for DecomposeBits {
    fn replace_vars_for_unroll(
        &mut self,
        iterator: &Var,
        unroll_index: usize,
        iterator_value: usize,
        internal_vars: &BTreeSet<Var>,
    ) {
        assert_ne!(&self.var, iterator, "Weird");
        if internal_vars.contains(&self.var) {
            self.var = format!("@unrolled_{unroll_index}_{iterator_value}_{}", self.var);
        }
        for expr in &mut self.to_decompose {
            crate::ir::unroll::replace_vars_for_unroll_in_expr(
                expr, iterator, unroll_index, iterator_value, internal_vars,
            );
        }
    }

    fn replace_vars_with_const(&mut self, map: &BTreeMap<Var, F>) {
        for expr in &mut self.to_decompose {
            crate::ir::utilities::replace_vars_by_const_in_expr(expr, map);
        }
    }

    fn get_function_calls(&self, function_calls: &mut Vec<String>) {
        for expr in &self.to_decompose {
            crate::ir::utilities::get_function_calls_in_expr(expr, function_calls);
        }
    }

    fn find_internal_vars(&self) -> (BTreeSet<Var>, BTreeSet<Var>) {
        let mut internal_vars = BTreeSet::new();
        let mut external_vars = BTreeSet::new();

        internal_vars.insert(self.var.clone());

        for expr in &self.to_decompose {
            let (expr_internal, expr_external) = crate::ir::utilities::find_internal_vars_in_expr(expr);
            internal_vars.extend(expr_internal);
            external_vars.extend(expr_external);
        }

        (internal_vars, external_vars)
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
