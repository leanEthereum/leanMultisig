//! Statement types and implementations.

pub mod array_assign;
pub mod assert;
pub mod assignment;
pub mod break_stmt;
pub mod counter_hint;
pub mod decompose_bits;
pub mod for_loop;
pub mod function_call;
pub mod function_ret;
pub mod if_condition;
pub mod location_report;
pub mod malloc;
pub mod match_stmt;
pub mod panic;
pub mod precompile;
pub mod print;

use crate::traits::IndentedDisplay;
use std::fmt::{Display, Formatter};

pub use array_assign::ArrayAssign;
pub use assert::Assert;
pub use assignment::Assignment;
pub use break_stmt::Break;
pub use counter_hint::CounterHint;
pub use decompose_bits::DecomposeBits;
pub use for_loop::ForLoop;
pub use function_call::FunctionCall;
pub use function_ret::FunctionRet;
pub use if_condition::IfCondition;
pub use location_report::LocationReport;
pub use malloc::MAlloc;
pub use match_stmt::Match;
pub use panic::Panic;
pub use precompile::PrecompileStmt;
pub use print::Print;

/// A statement in the Lean language.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Line {
    /// Pattern matching with computed jumps
    Match(Match),
    /// Variable assignment with expressions
    Assignment(Assignment),
    /// Array element assignment
    ArrayAssign(ArrayAssign),
    /// Runtime assertion checks
    Assert(Assert),
    /// Conditional branching (if-else)
    IfCondition(IfCondition),
    /// For loop iteration
    ForLoop(ForLoop),
    /// Function invocation with argument passing
    FunctionCall(FunctionCall),
    /// Function return with values
    FunctionRet(FunctionRet),
    /// Precompiled cryptographic operations
    Precompile(PrecompileStmt),
    /// Break statement for loop control
    Break(Break),
    /// Unconditional program termination
    Panic(Panic),
    /// Debug print statement
    Print(Print),
    /// Memory allocation
    MAlloc(MAlloc),
    /// Bit decomposition for field elements
    DecomposeBits(DecomposeBits),
    /// Counter value hint for loops
    CounterHint(CounterHint),
    /// Source location tracking for debugging
    LocationReport(LocationReport),
}

impl Display for Line {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Line::Match(stmt) => write!(f, "{}", stmt),
            Line::Assignment(stmt) => write!(f, "{}", stmt),
            Line::ArrayAssign(stmt) => write!(f, "{}", stmt),
            Line::Assert(stmt) => write!(f, "{}", stmt),
            Line::IfCondition(stmt) => write!(f, "{}", stmt),
            Line::ForLoop(stmt) => write!(f, "{}", stmt),
            Line::FunctionCall(stmt) => write!(f, "{}", stmt),
            Line::FunctionRet(stmt) => write!(f, "{}", stmt),
            Line::Precompile(stmt) => write!(f, "{}", stmt),
            Line::Break(stmt) => write!(f, "{}", stmt),
            Line::Panic(stmt) => write!(f, "{}", stmt),
            Line::Print(stmt) => write!(f, "{}", stmt),
            Line::MAlloc(stmt) => write!(f, "{}", stmt),
            Line::DecomposeBits(stmt) => write!(f, "{}", stmt),
            Line::CounterHint(stmt) => write!(f, "{}", stmt),
            Line::LocationReport(stmt) => write!(f, "{}", stmt),
        }
    }
}

impl IndentedDisplay for Line {
    fn to_string_with_indent(&self, indent: usize) -> String {
        match self {
            Line::Match(stmt) => stmt.to_string_with_indent(indent),
            Line::Assignment(stmt) => stmt.to_string_with_indent(indent),
            Line::ArrayAssign(stmt) => stmt.to_string_with_indent(indent),
            Line::Assert(stmt) => stmt.to_string_with_indent(indent),
            Line::IfCondition(stmt) => stmt.to_string_with_indent(indent),
            Line::ForLoop(stmt) => stmt.to_string_with_indent(indent),
            Line::FunctionCall(stmt) => stmt.to_string_with_indent(indent),
            Line::FunctionRet(stmt) => stmt.to_string_with_indent(indent),
            Line::Precompile(stmt) => stmt.to_string_with_indent(indent),
            Line::Break(stmt) => stmt.to_string_with_indent(indent),
            Line::Panic(stmt) => stmt.to_string_with_indent(indent),
            Line::Print(stmt) => stmt.to_string_with_indent(indent),
            Line::MAlloc(stmt) => stmt.to_string_with_indent(indent),
            Line::DecomposeBits(stmt) => stmt.to_string_with_indent(indent),
            Line::CounterHint(stmt) => stmt.to_string_with_indent(indent),
            Line::LocationReport(stmt) => stmt.to_string_with_indent(indent),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::{
        ast::types::Boolean,
        expr::{Expression, SimpleExpr},
    };

    #[test]
    fn test_line_assignment_display() {
        let line = Line::Assignment(Assignment {
            var: "x".to_string(),
            value: Expression::scalar(42),
        });
        assert_eq!(line.to_string(), "x = 42");
    }

    #[test]
    fn test_line_panic_display() {
        let line = Line::Panic(Panic);
        assert_eq!(line.to_string(), "panic");
    }

    #[test]
    fn test_line_break_display() {
        let line = Line::Break(Break);
        assert_eq!(line.to_string(), "break");
    }

    #[test]
    fn test_line_assert_display() {
        let line = Line::Assert(Assert {
            condition: Boolean::Equal {
                left: Expression::Value(SimpleExpr::Var("x".to_string())),
                right: Expression::scalar(10),
            },
        });
        assert_eq!(line.to_string(), "assert x == 10");
    }

    #[test]
    fn test_line_indented_display() {
        let line = Line::Assignment(Assignment {
            var: "y".to_string(),
            value: Expression::scalar(100),
        });
        assert_eq!(line.to_string_with_indent(2), "        y = 100");
    }
}
