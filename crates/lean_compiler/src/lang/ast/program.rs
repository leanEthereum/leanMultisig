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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::{Expression, SimpleExpr};

    #[test]
    fn test_function_has_const_arguments() {
        let func_with_const = Function {
            name: "test".to_string(),
            arguments: vec![("x".to_string(), false), ("y".to_string(), true)],
            inlined: false,
            n_returned_vars: 1,
            body: vec![],
        };
        assert!(func_with_const.has_const_arguments());

        let func_no_const = Function {
            name: "test".to_string(),
            arguments: vec![("x".to_string(), false), ("y".to_string(), false)],
            inlined: false,
            n_returned_vars: 1,
            body: vec![],
        };
        assert!(!func_no_const.has_const_arguments());
    }

    #[test]
    fn test_function_display_empty_body() {
        let func = Function {
            name: "empty_fn".to_string(),
            arguments: vec![("x".to_string(), false)],
            inlined: false,
            n_returned_vars: 0,
            body: vec![],
        };
        assert_eq!(func.to_string(), "fn empty_fn(x) -> 0 {}");
    }

    #[test]
    fn test_function_display_with_const_args() {
        let func = Function {
            name: "const_fn".to_string(),
            arguments: vec![("x".to_string(), true), ("y".to_string(), false)],
            inlined: false,
            n_returned_vars: 1,
            body: vec![],
        };
        assert_eq!(func.to_string(), "fn const_fn(const x, y) -> 1 {}");
    }

    #[test]
    fn test_program_display() {
        let mut program = Program {
            functions: BTreeMap::new(),
        };

        let func = Function {
            name: "test".to_string(),
            arguments: vec![],
            inlined: false,
            n_returned_vars: 0,
            body: vec![],
        };

        program.functions.insert("test".to_string(), func);
        assert_eq!(program.to_string(), "fn test() -> 0 {}");
    }

    #[test]
    fn test_program_multiple_functions_display() {
        let mut program = Program {
            functions: BTreeMap::new(),
        };

        let func1 = Function {
            name: "func1".to_string(),
            arguments: vec![],
            inlined: false,
            n_returned_vars: 0,
            body: vec![],
        };

        let func2 = Function {
            name: "func2".to_string(),
            arguments: vec![],
            inlined: false,
            n_returned_vars: 1,
            body: vec![],
        };

        program.functions.insert("func1".to_string(), func1);
        program.functions.insert("func2".to_string(), func2);

        let result = program.to_string();
        assert_eq!(result, "fn func1() -> 0 {}\nfn func2() -> 1 {}");
    }

    #[test]
    fn test_function_display_with_body() {
        let func = Function {
            name: "test_func".to_string(),
            arguments: vec![("x".to_string(), false)],
            inlined: false,
            n_returned_vars: 1,
            body: vec![
                Line::Assignment {
                    var: "result".to_string(),
                    value: Expression::scalar(42),
                },
                Line::FunctionRet {
                    return_data: vec![Expression::Value(SimpleExpr::Var("result".to_string()))],
                },
            ],
        };
        assert_eq!(
            func.to_string(),
            "fn test_func(x) -> 1 {\n    result = 42\n    return result\n}"
        );
    }
}
