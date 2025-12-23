use crate::lang::FileId;
use crate::parser::{
    error::{ParseResult, SemanticError},
    grammar::{ParsePair, Rule},
};
use std::collections::{BTreeMap, BTreeSet};

pub mod expression;
pub mod function;
pub mod literal;
pub mod program;
pub mod statement;

/// Represents a parsed constant value (scalar or array).
#[derive(Debug, Clone)]
pub enum ParsedConstant {
    Scalar(usize),
    Array(Vec<usize>),
}

/// Core parsing context that all parsers share.
#[derive(Debug)]
pub struct ParseContext {
    /// Compile-time scalar constants defined in the program
    pub constants: BTreeMap<String, usize>,
    /// Compile-time array constants defined in the program
    pub const_arrays: BTreeMap<String, Vec<usize>>,
    /// Counter for generating unique trash variable names
    pub trash_var_count: usize,
    /// Filepath of the file we are currently parsing
    pub current_filepath: String,
    /// Source code of the file we are currently parsing
    pub current_source_code: String,
    /// File ID of the file we are currently parsing
    pub current_file_id: FileId,
    /// Absolute filepaths imported so far (also includes the root filepath)
    pub imported_filepaths: BTreeSet<String>,
    /// Next unused file ID
    pub next_file_id: usize,
}

impl ParseContext {
    pub fn new(current_filepath: &str, current_source_code: &str) -> Self {
        Self {
            constants: BTreeMap::new(),
            const_arrays: BTreeMap::new(),
            trash_var_count: 0,
            current_filepath: current_filepath.to_string(),
            current_file_id: 0,
            imported_filepaths: BTreeSet::new(),
            current_source_code: current_source_code.to_string(),
            next_file_id: 1,
        }
    }

    /// Adds a scalar constant to the context.
    pub fn add_constant(&mut self, name: String, value: usize) -> Result<(), SemanticError> {
        if self.constants.contains_key(&name) || self.const_arrays.contains_key(&name) {
            Err(SemanticError::with_context(
                format!("Defined multiple times: {name}"),
                "constant declaration",
            ))
        } else {
            self.constants.insert(name, value);
            Ok(())
        }
    }

    /// Adds an array constant to the context.
    pub fn add_const_array(&mut self, name: String, values: Vec<usize>) -> Result<(), SemanticError> {
        if self.constants.contains_key(&name) || self.const_arrays.contains_key(&name) {
            Err(SemanticError::with_context(
                format!("Defined multiple times: {name}"),
                "constant declaration",
            ))
        } else {
            self.const_arrays.insert(name, values);
            Ok(())
        }
    }

    /// Looks up a scalar constant value.
    pub fn get_constant(&self, name: &str) -> Option<usize> {
        self.constants.get(name).copied()
    }

    /// Looks up an array constant.
    pub fn get_const_array(&self, name: &str) -> Option<&Vec<usize>> {
        self.const_arrays.get(name)
    }

    /// Generates a unique trash variable name.
    pub fn next_trash_var(&mut self) -> String {
        self.trash_var_count += 1;
        format!("@trash_{}", self.trash_var_count)
    }

    /// Returns a fresh file id.
    pub fn get_next_file_id(&mut self) -> FileId {
        let file_id = self.next_file_id;
        self.next_file_id += 1;
        file_id
    }
}

impl Default for ParseContext {
    fn default() -> Self {
        Self::new("<string>", "")
    }
}

/// Core trait for all parsers in the system.
pub trait Parse<T>: Sized {
    /// Parses the given input into the target type.
    fn parse(&self, pair: ParsePair<'_>, ctx: &mut ParseContext) -> ParseResult<T>;
}

/// Utility function to expect a specific rule type.
pub fn expect_rule(pair: &ParsePair<'_>, expected: Rule) -> ParseResult<()> {
    if pair.as_rule() == expected {
        Ok(())
    } else {
        Err(SemanticError::new(format!("Expected {:?} but found {:?}", expected, pair.as_rule())).into())
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
