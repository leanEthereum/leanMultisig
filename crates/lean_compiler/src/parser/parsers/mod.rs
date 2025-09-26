use crate::parser::{
    error::{ParseResult, SemanticError},
    grammar::{ParsePair, Rule},
};
use std::collections::BTreeMap;

pub mod expression;
pub mod function;
pub mod literal;
pub mod program;
pub mod statement;

/// Core parsing context that all parsers share.
#[derive(Debug)]
pub struct ParseContext {
    /// Compile-time constants defined in the program
    pub constants: BTreeMap<String, usize>,
    /// Counter for generating unique trash variable names
    pub trash_var_count: usize,
}

impl ParseContext {
    pub const fn new() -> Self {
        Self {
            constants: BTreeMap::new(),
            trash_var_count: 0,
        }
    }

    /// Adds a constant to the context.
    pub fn add_constant(&mut self, name: String, value: usize) -> Result<(), SemanticError> {
        if self.constants.insert(name.clone(), value).is_some() {
            Err(SemanticError::with_context(
                format!("Multiply defined constant: {}", name),
                "constant declaration",
            ))
        } else {
            Ok(())
        }
    }

    /// Looks up a constant value.
    pub fn get_constant(&self, name: &str) -> Option<usize> {
        self.constants.get(name).copied()
    }

    /// Generates a unique trash variable name.
    pub fn next_trash_var(&mut self) -> String {
        self.trash_var_count += 1;
        format!("@trash_{}", self.trash_var_count)
    }
}

impl Default for ParseContext {
    fn default() -> Self {
        Self::new()
    }
}

/// Core trait for all parsers in the system.
pub trait Parse<T>: Sized {
    /// Parses the given input into the target type.
    fn parse(pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<T>;
}

/// Utility function to expect a specific rule type.
pub fn expect_rule(pair: &ParsePair<'_>, expected: Rule) -> ParseResult<()> {
    if pair.as_rule() == expected {
        Ok(())
    } else {
        Err(SemanticError::new(format!(
            "Expected {:?} but found {:?}",
            expected,
            pair.as_rule()
        ))
        .into())
    }
}

/// Utility function to safely get the next inner pair with error handling.
pub fn next_inner_pair<'i>(
    pairs: &mut impl Iterator<Item = ParsePair<'i>>,
    context: &str,
) -> ParseResult<ParsePair<'i>> {
    pairs
        .next()
        .ok_or_else(|| SemanticError::with_context("Unexpected end of input", context).into())
}
