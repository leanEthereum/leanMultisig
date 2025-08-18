use std::{collections::BTreeMap, fmt};

use crate::lang::{Label, const_expr::ConstExpression};

pub mod intermediate_value;
pub use intermediate_value::*;
pub mod operation;
pub use operation::*;
pub mod instruction;
pub use instruction::*;

#[derive(Debug, Clone)]
pub struct IntermediateBytecode {
    pub bytecode: BTreeMap<Label, Vec<IntermediateInstruction>>,
    pub memory_size_per_function: BTreeMap<String, usize>,
}

impl fmt::Display for IntermediateBytecode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Iterate through each labeled block of instructions in the bytecode.
        for (label, instructions) in &self.bytecode {
            // Write the label for the current block, followed by a newline.
            writeln!(f, "\n{label}:")?;
            // Iterate through each instruction within the block.
            for instruction in instructions {
                // Write the instruction, indented with two spaces for readability.
                writeln!(f, "  {instruction}")?;
            }
        }

        // Write the header for the memory size section.
        writeln!(f, "\nMemory size per function:")?;
        // Iterate through the recorded memory sizes for each function.
        for (function_name, size) in &self.memory_size_per_function {
            // Write the function name and its corresponding memory size.
            writeln!(f, "{function_name}: {size}")?;
        }

        // Return Ok to indicate that formatting was successful.
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IntermediaryMemOrFpOrConstant {
    MemoryAfterFp { offset: ConstExpression }, // m[fp + offset]
    Fp,
    Constant(ConstExpression),
}

impl fmt::Display for IntermediaryMemOrFpOrConstant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MemoryAfterFp { offset } => write!(f, "m[fp + {offset}]"),
            Self::Fp => write!(f, "fp"),
            Self::Constant(c) => write!(f, "{c}"),
        }
    }
}
