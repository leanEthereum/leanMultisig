//! Bytecode representation and management

use crate::{CodeAddress, Hint};

use super::Instruction;
use std::collections::BTreeMap;
use std::fmt::{Display, Formatter};

/// Complete bytecode representation with instructions and hints
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Bytecode {
    pub instructions: Vec<Instruction>,
    pub hints: BTreeMap<CodeAddress, Vec<Hint>>, // pc -> hints
    pub starting_frame_memory: usize,
    pub ending_pc: CodeAddress,
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
