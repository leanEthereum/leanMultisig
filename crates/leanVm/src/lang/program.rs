use std::{collections::BTreeMap, fmt};

use crate::lang::Function;

#[derive(Debug, Clone)]
pub struct Program {
    pub functions: BTreeMap<String, Function>,
}

impl fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let program_str = self
            .functions
            .values()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join("\n\n");

        // Write the final, joined string to the formatter.
        write!(f, "{program_str}")
    }
}
