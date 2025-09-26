//! Parser for Lean source code.

mod error;
mod grammar;
mod lexer;
mod parsers;

pub use error::ParseError;
pub use grammar::parse_source;
pub use parsers::program::ProgramParser;
pub use parsers::{Parse, ParseContext};

use crate::lang::Program;
use std::collections::BTreeMap;

/// Main entry point for parsing Lean programs.
pub fn parse_program(input: &str) -> Result<(Program, BTreeMap<usize, String>), ParseError> {
    // Preprocess source to remove comments
    let processed_input = lexer::preprocess_source(input);

    // Parse grammar into AST nodes
    let program_pair = parse_source(&processed_input)?;

    // Parse into semantic structures
    let mut ctx = ParseContext::new();
    ProgramParser::parse(program_pair, &mut ctx)
}
