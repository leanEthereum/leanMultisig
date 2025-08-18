use crate::parser::Rule;

#[derive(Debug)]
pub enum ParseError {
    PestError(Box<pest::error::Error<Rule>>),
    SemanticError(String),
}

impl From<pest::error::Error<Rule>> for ParseError {
    fn from(error: pest::error::Error<Rule>) -> Self {
        Self::PestError(Box::new(error))
    }
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::PestError(e) => write!(f, "Parse error: {e}"),
            Self::SemanticError(e) => write!(f, "Semantic error: {e}"),
        }
    }
}

impl std::error::Error for ParseError {}
