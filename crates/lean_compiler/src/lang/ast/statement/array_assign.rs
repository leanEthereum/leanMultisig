//! Array assignment statement implementation.

use crate::{
    lang::expr::{Expression, SimpleExpr},
    traits::IndentedDisplay,
};
use std::fmt::{Display, Formatter};

/// Array element assignment statement.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ArrayAssign {
    /// Target array expression
    pub array: SimpleExpr,
    /// Index expression
    pub index: Expression,
    /// Value expression to assign
    pub value: Expression,
}

impl Display for ArrayAssign {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}[{}] = {}", self.array, self.index, self.value)
    }
}

impl IndentedDisplay for ArrayAssign {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::expr::{Expression, SimpleExpr};

    #[test]
    fn test_array_assign_display() {
        let array_assign = ArrayAssign {
            array: SimpleExpr::Var("arr".to_string()),
            index: Expression::scalar(0),
            value: Expression::scalar(10),
        };
        assert_eq!(array_assign.to_string(), "arr[0] = 10");
    }

    #[test]
    fn test_array_assign_indented_display() {
        let array_assign = ArrayAssign {
            array: SimpleExpr::Var("data".to_string()),
            index: Expression::scalar(5),
            value: Expression::scalar(42),
        };
        assert_eq!(
            array_assign.to_string_with_indent(2),
            "        data[5] = 42"
        );
    }
}
