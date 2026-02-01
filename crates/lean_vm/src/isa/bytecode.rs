//! Bytecode representation and management

use p3_util::log2_ceil_usize;

use crate::{CodeAddress, F, FileId, FunctionName, Hint, N_INSTRUCTION_COLUMNS, SourceLocation};

use super::Instruction;
use std::collections::BTreeMap;
use std::fmt::{Display, Formatter};

/// Complete bytecode representation with instructions and hints
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Bytecode {
    pub instructions: Vec<Instruction>,
    pub instructions_encoded: Vec<[F; N_INSTRUCTION_COLUMNS]>, // padded to power of two length (with zero rows)
    pub instructions_multilinear: Vec<F>,
    pub hints: BTreeMap<CodeAddress, Vec<Hint>>,               // pc -> hints
    pub starting_frame_memory: usize,
    // debug
    pub function_locations: BTreeMap<SourceLocation, FunctionName>,
    pub filepaths: BTreeMap<FileId, String>,
    pub source_code: BTreeMap<FileId, String>,
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
                writeln!(f, "hint: {hint}")?;
            }
            writeln!(f, "{pc:>4}: {instruction}")?;
        }
        Ok(())
    }
}
