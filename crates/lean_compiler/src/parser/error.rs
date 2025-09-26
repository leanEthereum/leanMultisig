use pest::error::Error as PestError;
use std::fmt::{Display, Formatter};

/// Comprehensive parsing error type.
#[derive(Debug)]
pub enum ParseError {
    /// Low-level syntax error from the grammar parser
    SyntaxError(Box<PestError<crate::parser::grammar::Rule>>),

    /// High-level semantic validation error
    SemanticError(SemanticError),
}

/// Semantic errors that occur during AST construction and validation.
#[derive(Debug)]
pub struct SemanticError {
    /// Human-readable error message
    pub message: String,
    /// Optional context about where the error occurred
    pub context: Option<String>,
}

impl SemanticError {
    /// Creates a new semantic error with just a message.
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            context: None,
        }
    }

    /// Creates a semantic error with additional context.
    pub fn with_context(message: impl Into<String>, context: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            context: Some(context.into()),
        }
    }
}

impl From<Box<PestError<crate::parser::grammar::Rule>>> for ParseError {
    fn from(error: Box<PestError<crate::parser::grammar::Rule>>) -> Self {
        Self::SyntaxError(error)
    }
}

impl From<SemanticError> for ParseError {
    fn from(error: SemanticError) -> Self {
        Self::SemanticError(error)
    }
}

impl From<String> for ParseError {
    fn from(message: String) -> Self {
        Self::SemanticError(SemanticError::new(message))
    }
}

impl Display for SemanticError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)?;
        if let Some(context) = &self.context {
            write!(f, " (in {})", context)?;
        }
        Ok(())
    }
}

impl Display for ParseError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SyntaxError(e) => write!(f, "Syntax error: {e}"),
            Self::SemanticError(e) => write!(f, "Semantic error: {e}"),
        }
    }
}

impl std::error::Error for SemanticError {}
impl std::error::Error for ParseError {}

/// Result type for parsing operations.
pub type ParseResult<T> = Result<T, ParseError>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_semantic_error_new() {
        let error = SemanticError::new("test message");
        assert_eq!(error.message, "test message");
        assert_eq!(error.context, None);
    }

    #[test]
    fn test_semantic_error_with_context() {
        let error = SemanticError::with_context("test message", "test context");
        assert_eq!(error.message, "test message");
        assert_eq!(error.context, Some("test context".to_string()));
    }

    #[test]
    fn test_semantic_error_display() {
        let error = SemanticError::new("test message");
        assert_eq!(error.to_string(), "test message");

        let error_with_context = SemanticError::with_context("test message", "test context");
        assert_eq!(
            error_with_context.to_string(),
            "test message (in test context)"
        );
    }

    #[test]
    fn test_parse_error_from_string() {
        let error: ParseError = "test message".to_string().into();
        if let ParseError::SemanticError(semantic_error) = error {
            assert_eq!(semantic_error.message, "test message");
            assert_eq!(semantic_error.context, None);
        } else {
            panic!("Expected SemanticError");
        }
    }

    #[test]
    fn test_parse_error_from_semantic_error() {
        let semantic_error = SemanticError::new("test");
        let parse_error: ParseError = semantic_error.into();
        if let ParseError::SemanticError(se) = parse_error {
            assert_eq!(se.message, "test");
        } else {
            panic!("Expected SemanticError variant");
        }
    }

    #[test]
    fn test_parse_error_display() {
        let semantic_error = SemanticError::new("semantic test");
        let parse_error = ParseError::SemanticError(semantic_error);
        assert_eq!(parse_error.to_string(), "Semantic error: semantic test");
    }
}
