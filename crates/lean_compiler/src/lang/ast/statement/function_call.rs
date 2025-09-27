//! Function call statement implementation.

use crate::{
    lang::{expr::Expression, values::Var},
    traits::IndentedDisplay,
};
use std::fmt::{Display, Formatter};

/// Function call statement.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FunctionCall {
    /// Name of the function to call
    pub function_name: String,
    /// Arguments to pass to the function
    pub args: Vec<Expression>,
    /// Variables to store return values
    pub return_data: Vec<Var>,
}

impl Display for FunctionCall {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let args_str = self.args
            .iter()
            .map(|arg| format!("{arg}"))
            .collect::<Vec<_>>()
            .join(", ");
        let return_data_str = self.return_data
            .iter()
            .map(|var| var.to_string())
            .collect::<Vec<_>>()
            .join(", ");

        if self.return_data.is_empty() {
            write!(f, "{}({args_str})", self.function_name)
        } else {
            write!(f, "{return_data_str} = {}({args_str})", self.function_name)
        }
    }
}

impl IndentedDisplay for FunctionCall {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::expr::Expression;

    #[test]
    fn test_function_call_with_return_display() {
        let call = FunctionCall {
            function_name: "test_fn".to_string(),
            args: vec![Expression::scalar(1), Expression::scalar(2)],
            return_data: vec!["result".to_string()],
        };
        assert_eq!(call.to_string(), "result = test_fn(1, 2)");
    }

    #[test]
    fn test_function_call_no_return_display() {
        let call = FunctionCall {
            function_name: "void_fn".to_string(),
            args: vec![Expression::scalar(42)],
            return_data: vec![],
        };
        assert_eq!(call.to_string(), "void_fn(42)");
    }

    #[test]
    fn test_function_call_multiple_returns() {
        let call = FunctionCall {
            function_name: "multi_fn".to_string(),
            args: vec![],
            return_data: vec!["a".to_string(), "b".to_string()],
        };
        assert_eq!(call.to_string(), "a, b = multi_fn()");
    }
}