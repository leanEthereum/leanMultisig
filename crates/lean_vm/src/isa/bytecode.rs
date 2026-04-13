//! Bytecode representation and management

use backend::*;
use serde::{Deserialize, Serialize};

use crate::{CodeAddress, EF, F, FileId, FunctionName, Hint, SourceLocation};

use super::Instruction;
use std::collections::BTreeMap;
use std::fmt::{Display, Formatter};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Bytecode {
    pub instructions: Vec<Instruction>,
    #[serde(skip)]
    pub instructions_multilinear: Vec<F>,
    #[serde(skip)]
    pub instructions_multilinear_packed: Vec<EFPacking<EF>>,
    pub hints: BTreeMap<CodeAddress, Vec<Hint>>,
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
        self.instructions.len()
    }

    pub fn padded_size(&self) -> usize {
        self.size().next_power_of_two()
    }

    pub fn log_size(&self) -> usize {
        log2_ceil_usize(self.size())
    }
}

impl Display for Bytecode {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for (pc, instruction) in self.instructions.iter().enumerate() {
            for hint in self.hints.get(&pc).unwrap_or(&Vec::new()) {
                if !matches!(hint, Hint::LocationReport { .. }) {
                    writeln!(f, "hint: {hint}")?;
                }
            }
            writeln!(f, "{pc:>4}: {instruction}")?;
        }
        Ok(())
    }
}
