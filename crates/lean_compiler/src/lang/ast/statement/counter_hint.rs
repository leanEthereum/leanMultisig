//! Counter hint statement implementation.

use crate::{
    lang::values::Var,
    traits::IndentedDisplay,
};
use std::fmt::{Display, Formatter};

/// Counter value hint statement for loops.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CounterHint {
    /// Variable to store the counter hint
    pub var: Var,
}

impl Display for CounterHint {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} = counter_hint({})", self.var, self.var)
    }
}

impl IndentedDisplay for CounterHint {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_counter_hint_display() {
        let hint = CounterHint {
            var: "counter".to_string(),
        };
        assert_eq!(hint.to_string(), "counter = counter_hint(counter)");
    }

    #[test]
    fn test_counter_hint_indented_display() {
        let hint = CounterHint {
            var: "loop_counter".to_string(),
        };
        assert_eq!(hint.to_string_with_indent(3), "            loop_counter = counter_hint(loop_counter)");
    }
}