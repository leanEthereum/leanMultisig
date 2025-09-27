//! Precompile statement implementation.

use crate::{
    F,
    lang::{expr::Expression, values::Var},
    precompiles::Precompile,
    traits::IndentedDisplay,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::{Display, Formatter},
};

use super::traits::StatementAnalysis;

/// Precompiled cryptographic operation statement.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PrecompileStmt {
    /// The precompile operation to execute
    pub precompile: Precompile,
    /// Arguments to pass to the precompile
    pub args: Vec<Expression>,
}

impl Display for PrecompileStmt {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}({})",
            self.precompile.name,
            self.args
                .iter()
                .map(|arg| format!("{arg}"))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

impl IndentedDisplay for PrecompileStmt {}

impl StatementAnalysis for PrecompileStmt {
    fn replace_vars_for_unroll(
        &mut self,
        iterator: &Var,
        unroll_index: usize,
        iterator_value: usize,
        internal_vars: &BTreeSet<Var>,
    ) {
        for arg in &mut self.args {
            crate::ir::unroll::replace_vars_for_unroll_in_expr(
                arg, iterator, unroll_index, iterator_value, internal_vars,
            );
        }
    }

    fn replace_vars_with_const(&mut self, map: &BTreeMap<Var, F>) {
        for arg in &mut self.args {
            crate::ir::utilities::replace_vars_by_const_in_expr(arg, map);
        }
    }

    fn get_function_calls(&self, function_calls: &mut Vec<String>) {
        for arg in &self.args {
            crate::ir::utilities::get_function_calls_in_expr(arg, function_calls);
        }
    }

    fn find_internal_vars(&self) -> (BTreeSet<Var>, BTreeSet<Var>) {
        let mut internal_vars = BTreeSet::new();
        let mut external_vars = BTreeSet::new();

        for arg in &self.args {
            let (arg_internal, arg_external) = crate::ir::utilities::find_internal_vars_in_expr(arg);
            internal_vars.extend(arg_internal);
            external_vars.extend(arg_external);
        }

        (internal_vars, external_vars)
    }
}



#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::expr::Expression;

    #[test]
    fn test_precompile_display() {
        let precompile_stmt = PrecompileStmt {
            precompile: crate::precompiles::POSEIDON_16,
            args: vec![Expression::scalar(1), Expression::scalar(2)],
        };
        assert_eq!(precompile_stmt.to_string(), "poseidon16(1, 2)");
    }

    #[test]
    fn test_precompile_no_args() {
        let precompile_stmt = PrecompileStmt {
            precompile: crate::precompiles::POSEIDON_16,
            args: vec![],
        };
        assert_eq!(precompile_stmt.to_string(), "poseidon16()");
    }
}
