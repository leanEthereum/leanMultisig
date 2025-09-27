//! Match statement implementation.

use crate::{lang::expr::Expression, traits::IndentedDisplay};
use std::fmt::{Display, Formatter};

/// Pattern matching statement.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Match {
    /// Expression to match against
    pub value: Expression,
    /// Match arms with patterns and bodies
    pub arms: Vec<(usize, Vec<super::Line>)>,
}

impl Display for Match {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let arms_str = self
            .arms
            .iter()
            .map(|(const_expr, body)| {
                let body_str = body
                    .iter()
                    .map(|line| line.to_string_with_indent(1))
                    .collect::<Vec<_>>()
                    .join("\n");
                format!("{const_expr} => {{\n{body_str}\n}}")
            })
            .collect::<Vec<_>>()
            .join("\n");
        write!(f, "match {} {{\n{arms_str}\n}}", self.value)
    }
}

impl IndentedDisplay for Match {
    fn to_string_with_indent(&self, indent: usize) -> String {
        let spaces = "    ".repeat(indent);
        let arms_str = self
            .arms
            .iter()
            .map(|(const_expr, body)| {
                let body_str = body
                    .iter()
                    .map(|line| line.to_string_with_indent(indent + 1))
                    .collect::<Vec<_>>()
                    .join("\n");
                format!("{const_expr} => {{\n{body_str}\n{spaces}}}")
            })
            .collect::<Vec<_>>()
            .join("\n");
        format!("{spaces}match {} {{\n{arms_str}\n{spaces}}}", self.value)
    }
}
