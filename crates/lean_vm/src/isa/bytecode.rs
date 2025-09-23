//! Bytecode representation and management

use super::Instruction;
use super::operands::Hint;
use std::collections::BTreeMap;
use std::fmt::{Display, Formatter};

/// Complete bytecode representation with instructions and hints
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Bytecode {
    pub instructions: Vec<Instruction>,
    pub hints: BTreeMap<usize, Vec<Hint>>, // pc -> hints
    pub starting_frame_memory: usize,
    pub ending_pc: usize,
}

impl Bytecode {
    /// Create new bytecode with the given instructions
    pub fn new(instructions: Vec<Instruction>) -> Self {
        Self {
            ending_pc: instructions.len().saturating_sub(1),
            instructions,
            hints: BTreeMap::new(),
            starting_frame_memory: 0,
        }
    }

    /// Add a hint at the specified program counter
    pub fn add_hint(&mut self, pc: usize, hint: Hint) {
        self.hints.entry(pc).or_default().push(hint);
    }

    /// Get hints for a specific program counter
    pub fn get_hints(&self, pc: usize) -> &[Hint] {
        self.hints.get(&pc).map_or(&[], |v| v.as_slice())
    }

    /// Get the number of instructions
    pub const fn len(&self) -> usize {
        self.instructions.len()
    }

    /// Check if bytecode is empty
    pub const fn is_empty(&self) -> bool {
        self.instructions.is_empty()
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
