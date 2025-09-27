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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::grammar::Rule;

    #[test]
    fn test_parse_context_new() {
        let ctx = ParseContext::new();
        assert!(ctx.constants.is_empty());
        assert_eq!(ctx.trash_var_count, 0);
    }

    #[test]
    fn test_parse_context_default() {
        let ctx = ParseContext::default();
        assert!(ctx.constants.is_empty());
        assert_eq!(ctx.trash_var_count, 0);
    }

    #[test]
    fn test_add_constant_success() {
        let mut ctx = ParseContext::new();
        let result = ctx.add_constant("test".to_string(), 42);
        assert!(result.is_ok());
        assert_eq!(ctx.get_constant("test"), Some(42));
    }

    #[test]
    fn test_add_constant_duplicate() {
        let mut ctx = ParseContext::new();
        ctx.add_constant("test".to_string(), 42).unwrap();
        let result = ctx.add_constant("test".to_string(), 24);
        assert!(result.is_err());
        if let Err(error) = result {
            assert!(error.message.contains("Multiply defined constant"));
        }
    }

    #[test]
    fn test_get_constant_exists() {
        let mut ctx = ParseContext::new();
        ctx.add_constant("test".to_string(), 42).unwrap();
        assert_eq!(ctx.get_constant("test"), Some(42));
    }

    #[test]
    fn test_get_constant_not_exists() {
        let ctx = ParseContext::new();
        assert_eq!(ctx.get_constant("missing"), None);
    }

    #[test]
    fn test_next_trash_var() {
        let mut ctx = ParseContext::new();
        let first = ctx.next_trash_var();
        let second = ctx.next_trash_var();

        assert_eq!(first, "@trash_1");
        assert_eq!(second, "@trash_2");
        assert_eq!(ctx.trash_var_count, 2);
    }

    #[test]
    fn test_expect_rule_success() {
        use crate::parser::grammar::LangParser;
        use pest::Parser;

        let input = "fn main() {}";
        let mut pairs = LangParser::parse(Rule::program, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = expect_rule(&pair, Rule::program);
        assert!(result.is_ok());
    }

    #[test]
    fn test_expect_rule_failure() {
        use crate::parser::grammar::LangParser;
        use pest::Parser;

        let input = "fn main() {}";
        let mut pairs = LangParser::parse(Rule::program, input).unwrap();
        let pair = pairs.next().unwrap();

        let result = expect_rule(&pair, Rule::function);
        assert!(result.is_err());
    }

    #[test]
    fn test_next_inner_pair_success() {
        use crate::parser::grammar::LangParser;
        use pest::Parser;

        let input = "fn main() {}";
        let mut pairs = LangParser::parse(Rule::program, input).unwrap();
        let pair = pairs.next().unwrap();
        let mut inner = pair.into_inner();

        let result = next_inner_pair(&mut inner, "test context");
        assert!(result.is_ok());
    }

    #[test]
    fn test_next_inner_pair_failure() {
        let mut empty_iter = std::iter::empty();
        let result = next_inner_pair(&mut empty_iter, "test context");
        assert!(result.is_err());
        if let Err(error) = result {
            if let crate::parser::error::ParseError::SemanticError(se) = error {
                assert_eq!(se.message, "Unexpected end of input");
                assert_eq!(se.context, Some("test context".to_string()));
            } else {
                panic!("Expected SemanticError");
            }
        }
    }
}
