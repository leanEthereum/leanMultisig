//! Location report statement implementation.

use crate::{F, lang::values::Var, traits::IndentedDisplay};
use lean_vm::SourceLineNumber;
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::{Display, Formatter},
};

use super::traits::{ReplaceVarsForUnroll, ReplaceVarsWithConst};

/// Source location tracking statement for debugging.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LocationReport {
    /// Source line number for debugging
    pub location: SourceLineNumber,
}

impl Display for LocationReport {
    fn fmt(&self, _f: &mut Formatter<'_>) -> std::fmt::Result {
        // Location reports don't display anything in the AST
        Ok(())
    }
}

impl IndentedDisplay for LocationReport {
    fn to_string_with_indent(&self, _indent: usize) -> String {
        // Location reports don't display anything
        String::new()
    }
}

impl ReplaceVarsForUnroll for LocationReport {
    fn replace_vars_for_unroll(
        &mut self,
        _iterator: &Var,
        _unroll_index: usize,
        _iterator_value: usize,
        _internal_vars: &BTreeSet<Var>,
    ) {
        // Location reports don't contain variables, so nothing to replace
    }
}

impl ReplaceVarsWithConst for LocationReport {
    fn replace_vars_with_const(&mut self, _map: &BTreeMap<Var, F>) {
        // Location reports don't contain variables, so nothing to replace
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_location_report_display() {
        let location = LocationReport { location: 42 };
        assert_eq!(location.to_string(), "");
    }

    #[test]
    fn test_location_report_indented() {
        let location = LocationReport { location: 123 };
        assert_eq!(location.to_string_with_indent(5), "");
    }
}
