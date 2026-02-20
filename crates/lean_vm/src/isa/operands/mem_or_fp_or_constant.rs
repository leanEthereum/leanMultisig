use crate::core::F;
use crate::diagnostics::RunnerError;
use crate::execution::Memory;
use backend::*;
use std::fmt::{Display, Formatter};

/// Memory, frame pointer, or constant operand
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MemOrFpOrConstant {
    /// memory[fp + offset]
    MemoryAfterFp { offset: usize },
    /// offset + offset
    FpRelative { offset: usize },
    /// Direct constant value
    Constant(F),
}

impl MemOrFpOrConstant {
    /// Read the value from memory, return fp, or return the constant
    pub fn read_value(&self, memory: &Memory, fp: usize) -> Result<F, RunnerError> {
        match self {
            Self::MemoryAfterFp { offset } => memory.get(fp + *offset),
            Self::FpRelative { offset } => Ok(F::from_usize(fp + *offset)),
            Self::Constant(c) => Ok(*c),
        }
    }

    /// Check if the value is unknown (would error when read)
    pub fn is_value_unknown(&self, memory: &Memory, fp: usize) -> bool {
        self.read_value(memory, fp).is_err()
    }

    /// Get the memory address (returns error for Fp and constants)
    pub const fn memory_address(&self, fp: usize) -> Result<usize, RunnerError> {
        match self {
            Self::MemoryAfterFp { offset } => Ok(fp + *offset),
            Self::FpRelative { .. } => Err(RunnerError::NotAPointer),
            Self::Constant(_) => Err(RunnerError::NotAPointer),
        }
    }
}

impl Display for MemOrFpOrConstant {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MemoryAfterFp { offset } => write!(f, "m[fp + {offset}]"),
            Self::FpRelative { offset } => write!(f, "fp + {offset}"),
            Self::Constant(c) => write!(f, "{c}"),
        }
    }
}
