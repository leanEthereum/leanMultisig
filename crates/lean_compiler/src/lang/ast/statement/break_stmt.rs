//! Break statement implementation.

use crate::{F, lang::values::Var, traits::IndentedDisplay};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::{Display, Formatter},
};

use super::traits::{ReplaceVarsForUnroll, ReplaceVarsWithConst};

/// Break statement for loop control.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Break;

impl Display for Break {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "break")
    }
}

impl IndentedDisplay for Break {}

impl ReplaceVarsForUnroll for Break {
    fn replace_vars_for_unroll(
        &mut self,
        _iterator: &Var,
        _unroll_index: usize,
        _iterator_value: usize,
        _internal_vars: &BTreeSet<Var>,
    ) {
        // Break statements don't contain variables, so nothing to replace
    }
}

impl ReplaceVarsWithConst for Break {
    fn replace_vars_with_const(&mut self, _map: &BTreeMap<Var, F>) {
        // Break statements don't contain variables, so nothing to replace
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_break_display() {
        let break_stmt = Break;
        assert_eq!(break_stmt.to_string(), "break");
    }

    #[test]
    fn test_break_indented_display() {
        let break_stmt = Break;
        assert_eq!(break_stmt.to_string_with_indent(1), "    break");
    }
}
