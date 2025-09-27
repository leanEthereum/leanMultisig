//! Memory allocation statement implementation.

use crate::{
    lang::{expr::Expression, values::Var},
    traits::IndentedDisplay,
};
use std::fmt::{Display, Formatter};

/// Memory allocation statement.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MAlloc {
    /// Variable to store the allocated memory pointer
    pub var: Var,
    /// Size of memory to allocate
    pub size: Expression,
    /// Whether this is vectorized allocation
    pub vectorized: bool,
    /// Length for vectorized allocation
    pub vectorized_len: Expression,
}

impl Display for MAlloc {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.vectorized {
            write!(
                f,
                "{} = malloc_vec({}, {})",
                self.var, self.size, self.vectorized_len
            )
        } else {
            write!(f, "{} = malloc({})", self.var, self.size)
        }
    }
}

impl IndentedDisplay for MAlloc {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::expr::Expression;

    #[test]
    fn test_malloc_display() {
        let malloc = MAlloc {
            var: "ptr".to_string(),
            size: Expression::scalar(100),
            vectorized: false,
            vectorized_len: Expression::scalar(1),
        };
        assert_eq!(malloc.to_string(), "ptr = malloc(100)");
    }

    #[test]
    fn test_malloc_vec_display() {
        let malloc_vec = MAlloc {
            var: "ptr".to_string(),
            size: Expression::scalar(100),
            vectorized: true,
            vectorized_len: Expression::scalar(8),
        };
        assert_eq!(malloc_vec.to_string(), "ptr = malloc_vec(100, 8)");
    }

    #[test]
    fn test_malloc_indented() {
        let malloc = MAlloc {
            var: "buffer".to_string(),
            size: Expression::scalar(256),
            vectorized: false,
            vectorized_len: Expression::scalar(1),
        };
        assert_eq!(
            malloc.to_string_with_indent(2),
            "        buffer = malloc(256)"
        );
    }
}
