use std::{
    collections::BTreeMap,
    fmt,
    fmt::{Display, Formatter},
};

pub mod operand;
pub use operand::*;
pub mod hint;
pub use hint::*;
pub mod operation;
pub use operation::*;
pub mod instruction;
pub use instruction::*;

pub type Label = String;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Bytecode {
    pub instructions: Vec<Instruction>,
    pub hints: BTreeMap<usize, Vec<Hint>>, // pc -> hints
    pub starting_frame_memory: usize,
    pub ending_pc: usize,
}

impl Display for Bytecode {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        for (pc, instruction) in self.instructions.iter().enumerate() {
            if let Some(hints) = self.hints.get(&pc) {
                for hint in hints {
                    writeln!(f, "hint: {hint}")?;
                }
            }
            writeln!(f, "{pc:>4}: {instruction}")?;
        }
        Ok(())
    }
}
