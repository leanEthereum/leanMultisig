use lean_vm::F;
use utils::ToUsize;

use crate::lang::FileId;
use crate::parser::{
    error::{ParseResult, SemanticError},
    grammar::{ParsePair, Rule},
};
use crate::{CompilationFlags, ProgramSource};
use std::collections::{BTreeMap, BTreeSet};

pub mod expression;
pub mod function;
pub mod literal;
pub mod program;
pub mod statement;

/// Represents a multi-dimensional constant array value.
/// Supports arbitrary nesting: `[[1, 2], [3, 4, 5], []]`
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConstArrayValue {
    Scalar(F),
    Array(Vec<ConstArrayValue>),
}

impl ConstArrayValue {
    pub fn len(&self) -> usize {
        match self {
            Self::Scalar(_) => panic!("Cannot get length of scalar value"),
            Self::Array(arr) => arr.len(),
        }
    }

    pub fn depth(&self) -> usize {
        match self {
            Self::Scalar(_) => 0,
            Self::Array(arr) => {
                if arr.is_empty() {
                    1
                } else {
                    1 + arr[0].depth()
                }
            }
        }
    }

    pub fn get(&self, idx: usize) -> Option<&Self> {
        match self {
            Self::Scalar(_) => None,
            Self::Array(arr) => arr.get(idx),
        }
    }

    pub fn as_scalar(&self) -> Option<F> {
        match self {
            Self::Scalar(v) => Some(*v),
            Self::Array(_) => None,
        }
    }

    pub fn navigate(&self, indices: &[F]) -> Option<&Self> {
        let mut current = self;
        for &idx in indices {
            current = current.get(idx.to_usize())?;
        }
        Some(current)
    }
}

/// Represents a parsed constant value (scalar or array).
#[derive(Debug, Clone)]
pub enum ParsedConstant {
    Scalar(F),
    Array(ConstArrayValue),
}

/// Core parsing context that all parsers share.
#[derive(Debug)]
pub struct ParseContext {
    /// Compile-time scalar constants defined in the program
    pub constants: BTreeMap<String, F>,
    /// Compile-time array constants defined in the program (supports nested arrays)
    pub const_arrays: BTreeMap<String, ConstArrayValue>,
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
    /// Stack of files currently being imported (for circular import detection)
    pub import_stack: Vec<String>,
    /// Root directory for resolving imports (directory of the entry point file)
    pub import_root: String,
    /// Next unused file ID
    pub next_file_id: usize,
    /// Compilation flags
    pub flags: CompilationFlags,
}

impl ParseContext {
    pub fn new(input: &ProgramSource, flags: CompilationFlags) -> Result<Self, SemanticError> {
        let current_source_code = input.get_content(&flags).unwrap();
        let (current_filepath, imported_filepaths) = match input {
            ProgramSource::Raw(_) => ("<raw_input>".to_string(), BTreeSet::new()),
            ProgramSource::Filepath(fp) => {
                let canonical = std::fs::canonicalize(fp)
                    .map_err(|e| SemanticError::new(format!("Cannot resolve filepath '{}': {}", fp, e)))?
                    .to_string_lossy()
                    .to_string();
                (canonical.clone(), [canonical].into_iter().collect())
            }
        };
        let import_stack = vec![current_filepath.clone()];
        let import_root = std::path::Path::new(&current_filepath)
            .parent()
            .map(|p| p.to_string_lossy().to_string())
            .unwrap_or_default();
        Ok(Self {
            constants: BTreeMap::new(),
            const_arrays: BTreeMap::new(),
            trash_var_count: 0,
            current_filepath,
            current_file_id: 0,
            imported_filepaths,
            import_stack,
            import_root,
            current_source_code,
            next_file_id: 1,
            flags,
        })
    }

    /// Adds a scalar constant to the context.
    pub fn add_constant(&mut self, name: String, value: F) -> Result<(), SemanticError> {
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
    pub fn add_const_array(&mut self, name: String, value: ConstArrayValue) -> Result<(), SemanticError> {
        if self.constants.contains_key(&name) || self.const_arrays.contains_key(&name) {
            Err(SemanticError::with_context(
                format!("Defined multiple times: {name}"),
                "constant declaration",
            ))
        } else {
            self.const_arrays.insert(name, value);
            Ok(())
        }
    }

    /// Looks up a scalar constant value.
    pub fn get_constant(&self, name: &str) -> Option<F> {
        self.constants.get(name).copied()
    }

    /// Looks up an array constant.
    pub fn get_const_array(&self, name: &str) -> Option<&ConstArrayValue> {
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
