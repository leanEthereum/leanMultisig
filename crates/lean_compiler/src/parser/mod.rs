//! Parser for Lean source code.

mod error;
mod grammar;
mod lexer;
mod parsers;

pub use error::ParseError;
pub use parsers::ConstArrayValue;
pub use parsers::program::parse_program;
