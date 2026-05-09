//! Bytecode representation and management

use backend::*;
use serde::{Deserialize, Serialize};

use crate::{DIMENSION, EF, F, FileId, FunctionName, Hint, N_INSTRUCTION_COLUMNS, SourceLocation};

use super::Instruction;
use std::collections::BTreeMap;
use std::fmt::{Display, Formatter};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CodeEntry {
    pub hints: Box<[Hint]>, // executed before the instruction
    pub instruction: Instruction,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Bytecode {
    pub code: Vec<CodeEntry>,
    pub instructions_multilinear: Vec<F>,
    /// SIMD-packed view of `instructions_multilinear` (platform-specific layout).
    /// Skipped during (de)serialization and recomputed via [`Bytecode::recompute_packed`].
    #[serde(skip, default)]
    pub instructions_multilinear_packed: Vec<EFPacking<EF>>, // embedded in the extension field(bad, TODO)
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
    /// Rebuild [`Self::instructions_multilinear_packed`] from `instructions_multilinear`.
    /// Used after deserializing from a cache (the packed layout is platform-specific
    /// and not portable, so we skip it on the wire and recompute locally).
    pub fn recompute_packed(&mut self) {
        self.instructions_multilinear_packed = pack_extension(
            &self
                .instructions_multilinear
                .iter()
                .map(|&pf| EF::from(pf))
                .collect::<Vec<EF>>(),
        );
    }

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
