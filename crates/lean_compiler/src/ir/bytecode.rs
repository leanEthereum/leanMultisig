use super::instruction::IntermediateInstruction;
use lean_vm::Label;
use std::collections::BTreeMap;
use std::fmt::{Display, Formatter};

/// Container for the complete intermediate representation of a program.
///
/// This structure holds all the compiled intermediate bytecode along with
/// metadata needed for execution and analysis.
#[derive(Debug, Clone)]
pub struct IntermediateBytecode {
    /// Main bytecode organized by function labels.
    ///
    /// Each label corresponds to a function entry point.
    pub bytecode: BTreeMap<Label, Vec<IntermediateInstruction>>,

    /// Match statement bytecode blocks.
    ///
    /// Each match statement produces multiple case blocks.
    pub match_blocks: Vec<Vec<Vec<IntermediateInstruction>>>,

    /// Memory requirements for each function.
    ///
    /// Maps function names to their stack frame size.
    pub memory_size_per_function: BTreeMap<String, usize>,
}

impl Display for IntermediateBytecode {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for (label, instructions) in &self.bytecode {
            writeln!(f, "\n{label}:")?;
            for instruction in instructions {
                writeln!(f, "  {instruction}")?;
            }
        }
        for (i, match_blocks) in self.match_blocks.iter().enumerate() {
            writeln!(f, "\nMatch {i}:")?;
            for (j, case) in match_blocks.iter().enumerate() {
                writeln!(f, "  Case {j}:")?;
                for instruction in case {
                    writeln!(f, "    {instruction}")?;
                }
            }
        }
        writeln!(f, "\nMemory size per function:")?;
        for (function_name, size) in &self.memory_size_per_function {
            writeln!(f, "{function_name}: {size}")?;
        }
        Ok(())
    }
}
