//! For loop statement implementation.

use crate::{
    lang::{expr::Expression, values::Var},
    traits::IndentedDisplay,
};
use std::fmt::{Display, Formatter};

/// For loop statement.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ForLoop {
    /// Iterator variable name
    pub iterator: Var,
    /// Start expression for the loop
    pub start: Expression,
    /// End expression for the loop
    pub end: Expression,
    /// Loop body statements
    pub body: Vec<super::Line>,
    /// Whether to iterate in reverse order
    pub rev: bool,
    /// Whether to unroll the loop
    pub unroll: bool,
}

impl Display for ForLoop {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let body_str = self
            .body
            .iter()
            .map(|line| line.to_string_with_indent(1))
            .collect::<Vec<_>>()
            .join("\n");
        write!(
            f,
            "for {} in {}..{} {}{}{{\n{}\n}}",
            self.iterator,
            self.start,
            self.end,
            if self.rev { "rev " } else { "" },
            if self.unroll { "unroll " } else { "" },
            body_str,
        )
    }
}

impl IndentedDisplay for ForLoop {
    fn to_string_with_indent(&self, indent: usize) -> String {
        let spaces = "    ".repeat(indent);
        let body_str = self
            .body
            .iter()
            .map(|line| line.to_string_with_indent(indent + 1))
            .collect::<Vec<_>>()
            .join("\n");
        format!(
            "{}for {} in {}..{} {}{}{{\n{}\n{}}}",
            spaces,
            self.iterator,
            self.start,
            self.end,
            if self.rev { "rev " } else { "" },
            if self.unroll { "unroll " } else { "" },
            body_str,
            spaces
        )
    }
}
