//! Bytecode representation and management

use backend::*;

use crate::{DIMENSION, F, FileId, FunctionName, Hint, N_INSTRUCTION_COLUMNS, SourceLocation};

use super::Instruction;
use std::collections::BTreeMap;
use std::fmt::{Display, Formatter};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CodeEntry {
    pub hints: Box<[Hint]>, // executed before the instruction
    pub instruction: Instruction,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Bytecode {
    pub code: Vec<CodeEntry>,
    pub instructions_multilinear: Vec<F>,
    pub starting_frame_memory: usize,
    pub hash: [F; DIGEST_ELEMS],
    // debug
    pub function_locations: BTreeMap<SourceLocation, FunctionName>,
    pub filepaths: BTreeMap<FileId, String>,
    pub source_code: BTreeMap<FileId, String>,
    /// Maps each pc to its source location (for error reporting)
    pub pc_to_location: Vec<SourceLocation>,
}

impl Bytecode {
    pub fn size(&self) -> usize {
        self.code.len()
    }

    pub fn padded_size(&self) -> usize {
        self.size().next_power_of_two()
    }

    pub fn log_size(&self) -> usize {
        log2_ceil_usize(self.size())
    }

    pub fn cumulated_n_vars(&self) -> usize {
        self.log_size() + log2_ceil_usize(N_INSTRUCTION_COLUMNS)
    }

    pub fn bytecode_claim_size(&self) -> usize {
        (self.cumulated_n_vars() + 1) * DIMENSION
    }
}

impl Display for Bytecode {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for (pc, entry) in self.code.iter().enumerate() {
            for hint in entry.hints.iter() {
                if !matches!(hint, Hint::LocationReport { .. }) {
                    writeln!(f, "hint: {hint}")?;
                }
            }
            writeln!(f, "{pc:>4}: {}", entry.instruction)?;
        }
        Ok(())
    }
}
