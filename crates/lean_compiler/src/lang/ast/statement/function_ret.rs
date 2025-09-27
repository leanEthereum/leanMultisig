//! Function return statement implementation.

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

/// Function return statement.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FunctionRet {
    /// Expressions to return from the function
    pub return_data: Vec<Expression>,
}

impl Display for FunctionRet {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let return_data_str = self
            .return_data
            .iter()
            .map(|arg| format!("{arg}"))
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "return {return_data_str}")
    }
}

impl IndentedDisplay for FunctionRet {}

impl ReplaceVarsForUnroll for FunctionRet {
    fn replace_vars_for_unroll(
        &mut self,
        iterator: &Var,
        unroll_index: usize,
        iterator_value: usize,
        internal_vars: &BTreeSet<Var>,
    ) {
        for ret in &mut self.return_data {
            crate::ir::unroll::replace_vars_for_unroll_in_expr(
                ret,
                iterator,
                unroll_index,
                iterator_value,
                internal_vars,
            );
        }
    }
}

impl ReplaceVarsWithConst for FunctionRet {
    fn replace_vars_with_const(&mut self, map: &BTreeMap<Var, F>) {
        for expr in &mut self.return_data {
            crate::ir::utilities::replace_vars_by_const_in_expr(expr, map);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::expr::Expression;

    #[test]
    fn test_function_ret_display() {
        let ret = FunctionRet {
            return_data: vec![Expression::scalar(1), Expression::scalar(2)],
        };
        assert_eq!(ret.to_string(), "return 1, 2");
    }

    #[test]
    fn test_function_ret_empty_display() {
        let ret = FunctionRet {
            return_data: vec![],
        };
        assert_eq!(ret.to_string(), "return ");
    }

    #[test]
    fn test_function_ret_single_value() {
        let ret = FunctionRet {
            return_data: vec![Expression::scalar(42)],
        };
        assert_eq!(ret.to_string(), "return 42");
    }
}
