//! Program and function definitions.

use std::collections::BTreeMap;
use std::fmt::{Display, Formatter};

use crate::lang::values::Var;

use super::stmt::Line;

/// A complete Lean program containing multiple functions.
#[derive(Debug, Clone)]
pub struct Program {
    /// Collection of all functions in the program indexed by name.
    pub functions: BTreeMap<String, Function>,
}

/// A function definition with arguments, body, and metadata.
#[derive(Debug, Clone)]
pub struct Function {
    /// Function name.
    pub name: String,
    /// Function arguments with const annotation.
    pub arguments: Vec<(Var, bool)>, // (name, is_const)
    /// Whether this function should be inlined during compilation.
    pub inlined: bool,
    /// Number of values returned by this function.
    pub n_returned_vars: usize,
    /// Function body as a sequence of statements.
    pub body: Vec<Line>,
}

impl Function {
    /// Returns true if this function has any const arguments.
    pub fn has_const_arguments(&self) -> bool {
        self.arguments.iter().any(|(_, is_const)| *is_const)
    }
}

impl Display for Program {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut first = true;
        for function in self.functions.values() {
            if !first {
                writeln!(f)?;
            }
            write!(f, "{function}")?;
            first = false;
        }
        Ok(())
    }
}

impl Display for Function {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
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
            .map(|line| format!("    {line}"))
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