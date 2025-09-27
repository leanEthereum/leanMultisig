//! Unified trait for statement operations.

use crate::{F, lang::Var};
use std::collections::{BTreeMap, BTreeSet};

/// Unified trait for all statement analysis and transformation operations.
pub trait StatementAnalysis {
    /// Replace variables for unrolling in this statement.
    fn replace_vars_for_unroll(
        &mut self,
        _iterator: &Var,
        _unroll_index: usize,
        _iterator_value: usize,
        _internal_vars: &BTreeSet<Var>,
    ) {
        // Default implementation: do nothing
    }

    /// Replace variables with constants in this statement.
    fn replace_vars_with_const(&mut self, _map: &BTreeMap<Var, F>) {
        // Default implementation: do nothing
    }

    /// Extract function calls from this statement.
    fn get_function_calls(&self, _function_calls: &mut Vec<String>) {
        // Default implementation: do nothing
    }

    /// Find internal and external variables in this statement.
    ///
    /// Returns (internal_vars, external_vars).
    fn find_internal_vars(&self) -> (BTreeSet<Var>, BTreeSet<Var>) {
        (BTreeSet::new(), BTreeSet::new())
    }
}
