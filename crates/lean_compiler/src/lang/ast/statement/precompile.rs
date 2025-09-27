//! Precompile statement implementation.

use crate::{
    lang::expr::Expression,
    precompiles::Precompile,
    traits::IndentedDisplay,
};
use std::fmt::{Display, Formatter};

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
            self.args.iter()
                .map(|arg| format!("{arg}"))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

impl IndentedDisplay for PrecompileStmt {}

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