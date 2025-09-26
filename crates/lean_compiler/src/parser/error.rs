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
