//! Parser for Lean source code.

mod error;
mod grammar;
mod lexer;
mod parsers;

pub use parsers::program::parse_program;
pub use parsers::ConstArrayValue;
