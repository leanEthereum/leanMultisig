//! Traits for statement operations.

use crate::{F, lang::Var};
use std::collections::{BTreeMap, BTreeSet};

/// Trait for replacing variables during loop unrolling.
pub trait ReplaceVarsForUnroll {
    /// Replace variables for unrolling in this statement.
    fn replace_vars_for_unroll(
        &mut self,
        iterator: &Var,
        unroll_index: usize,
        iterator_value: usize,
        internal_vars: &BTreeSet<Var>,
    );
}

/// Trait for replacing variables with constants.
pub trait ReplaceVarsWithConst {
    /// Replace variables with constants in this statement.
    fn replace_vars_with_const(&mut self, map: &BTreeMap<Var, F>);
}
