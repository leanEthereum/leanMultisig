//! Function return statement implementation.

use crate::{lang::expr::Expression, traits::IndentedDisplay};
use std::fmt::{Display, Formatter};

/// Function return statement.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FunctionRet {
    /// Expressions to return from the function
    pub return_data: Vec<Expression>,
}

impl Display for FunctionRet {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let return_data_str = self
            .return_data
            .iter()
            .map(|arg| format!("{arg}"))
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "return {return_data_str}")
    }
}

impl IndentedDisplay for FunctionRet {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::expr::Expression;

    #[test]
    fn test_function_ret_display() {
        let ret = FunctionRet {
            return_data: vec![Expression::scalar(1), Expression::scalar(2)],
        };
        assert_eq!(ret.to_string(), "return 1, 2");
    }

    #[test]
    fn test_function_ret_empty_display() {
        let ret = FunctionRet {
            return_data: vec![],
        };
        assert_eq!(ret.to_string(), "return ");
    }

    #[test]
    fn test_function_ret_single_value() {
        let ret = FunctionRet {
            return_data: vec![Expression::scalar(42)],
        };
        assert_eq!(ret.to_string(), "return 42");
    }
}
