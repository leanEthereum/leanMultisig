//! Print statement implementation.

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

impl StatementAnalysis for Print {
    fn replace_vars_for_unroll(
        &mut self,
        iterator: &Var,
        unroll_index: usize,
        iterator_value: usize,
        internal_vars: &BTreeSet<Var>,
    ) {
        self.line_info = format!(
            "{} (unrolled {} {})",
            self.line_info, unroll_index, iterator_value
        );
        for expr in &mut self.content {
            crate::ir::unroll::replace_vars_for_unroll_in_expr(
                expr,
                iterator,
                unroll_index,
                iterator_value,
                internal_vars,
            );
        }
    }

    fn replace_vars_with_const(&mut self, map: &BTreeMap<Var, F>) {
        for expr in &mut self.content {
            crate::ir::utilities::replace_vars_by_const_in_expr(expr, map);
        }
    }

    fn get_function_calls(&self, function_calls: &mut Vec<String>) {
        for expr in &self.content {
            crate::ir::utilities::get_function_calls_in_expr(expr, function_calls);
        }
    }

    fn find_internal_vars(&self) -> (BTreeSet<Var>, BTreeSet<Var>) {
        let mut internal_vars = BTreeSet::new();
        let mut external_vars = BTreeSet::new();

        for expr in &self.content {
            let (expr_internal, expr_external) =
                crate::ir::utilities::find_internal_vars_in_expr(expr);
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
