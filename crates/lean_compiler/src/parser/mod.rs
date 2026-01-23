//! Parser for Lean source code.

mod error;
mod grammar;
mod parsers;

pub use error::ParseError;
pub use parsers::ConstArrayValue;
pub use parsers::{function::RESERVED_FUNCTION_NAMES, program::parse_program};
