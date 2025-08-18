use std::fmt;

use crate::lang::{Line, Var};

#[derive(Debug, Clone)]
pub struct Function {
    pub name: String,
    pub arguments: Vec<(Var, bool)>, // (name, is_const)
    pub n_returned_vars: usize,
    pub body: Vec<Line>,
}

impl Function {
    #[must_use]
    pub fn has_const_arguments(&self) -> bool {
        self.arguments.iter().any(|(_, is_const)| *is_const)
    }
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let args_str = self
            .arguments
            .iter()
            .map(|arg| match arg {
                (name, true) => format!("const {name}"),
                (name, false) => name.to_string(),
            })
            .collect::<Vec<_>>()
            .join(", ");

        let instructions_str = self
            .body
            .iter()
            .map(|line| line.to_string_with_indent(1))
            .collect::<Vec<_>>()
            .join("\n");

        if self.body.is_empty() {
            write!(
                f,
                "fn {}({}) -> {} {{}}",
                self.name, args_str, self.n_returned_vars
            )
        } else {
            write!(
                f,
                "fn {}({}) -> {} {{\n{}\n}}",
                self.name, args_str, self.n_returned_vars, instructions_str
            )
        }
    }
}
