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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_program_simple() {
        let input = "fn main() {}";
        let result = parse_program(input);
        assert!(result.is_ok());

        if let Ok((program, locations)) = result {
            assert!(program.functions.contains_key("main"));
            assert!(!locations.is_empty());
        }
    }

    #[test]
    fn test_parse_program_with_comments() {
        let input = r#"
            // This is a comment
            fn main() {
                // Another comment
            }
        "#;
        let result = parse_program(input);
        assert!(result.is_ok());

        if let Ok((program, _)) = result {
            assert!(program.functions.contains_key("main"));
        }
    }

    #[test]
    fn test_parse_program_invalid_syntax() {
        let input = "invalid syntax $%@";
        let result = parse_program(input);
        assert!(result.is_err());
    }

    #[test]
    fn test_parse_program_multiple_functions() {
        let input = r#"
            fn first() {}
            fn second() {}
        "#;
        let result = parse_program(input);
        assert!(result.is_ok());

        if let Ok((program, locations)) = result {
            assert!(program.functions.contains_key("first"));
            assert!(program.functions.contains_key("second"));
            assert_eq!(locations.len(), 2);
        }
    }
}
