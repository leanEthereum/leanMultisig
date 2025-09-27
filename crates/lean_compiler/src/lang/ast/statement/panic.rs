//! Panic statement implementation.

use crate::{F, lang::values::Var, traits::IndentedDisplay};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::{Display, Formatter},
};

use super::traits::{ReplaceVarsForUnroll, ReplaceVarsWithConst};

/// Unconditional program termination.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Panic;

impl Display for Panic {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "panic")
    }
}

impl IndentedDisplay for Panic {}

impl ReplaceVarsForUnroll for Panic {
    fn replace_vars_for_unroll(
        &mut self,
        _iterator: &Var,
        _unroll_index: usize,
        _iterator_value: usize,
        _internal_vars: &BTreeSet<Var>,
    ) {
        // Panic statements don't contain variables, so nothing to replace
    }
}

impl ReplaceVarsWithConst for Panic {
    fn replace_vars_with_const(&mut self, _map: &BTreeMap<Var, F>) {
        // Panic statements don't contain variables, so nothing to replace
    }
}

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
