//! Main parser interface providing backward compatibility.
//!
//! This module re-exports the new modular parser implementation while maintaining
//! the existing public API for seamless integration with the rest of the compiler.

mod error;
mod lexer;
mod grammar;
mod parsers;

// Re-export the main parsing interface
pub use error::ParseError;
pub use grammar::parse_source;
pub use parsers::{ParseContext, Parse};
pub use parsers::program::ProgramParser;

use crate::lang::Program;
use std::collections::BTreeMap;

/// Main entry point for parsing Lean programs.
///
/// This function coordinates the entire parsing pipeline from source text
/// to a complete Program AST with location information.
pub fn parse_program(input: &str) -> Result<(Program, BTreeMap<usize, String>), ParseError> {
    // Preprocess source to remove comments
    let processed_input = lexer::preprocess_source(input);

    // Parse grammar into AST nodes
    let program_pair = parse_source(&processed_input)?;

    // Parse into semantic structures
    let mut ctx = ParseContext::new();
    ProgramParser::parse(program_pair, &mut ctx)
}
