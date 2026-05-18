use super::MemOrConstant;
use crate::core::F;
use crate::diagnostics::RunnerError;
use crate::execution::memory::MemoryAccess;
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
    pub fn read_value(&self, memory: &impl MemoryAccess, fp: usize) -> Result<F, RunnerError> {
        match self {
            Self::MemoryAfterFp { offset } => {
                let addr = fp.checked_add(*offset).ok_or(RunnerError::AddressOverflow)?;
                memory.get(addr)
            }
            Self::FpRelative { offset } => {
                let addr = fp.checked_add(*offset).ok_or(RunnerError::AddressOverflow)?;
                Ok(F::from_usize(addr))
            }
            Self::Constant(c) => Ok(*c),
        }
    }

    /// Check if the value is unknown (would error when read)
    pub fn is_value_unknown(&self, memory: &impl MemoryAccess, fp: usize) -> bool {
        self.read_value(memory, fp).is_err()
    }

    /// Get the memory address (returns error for Fp and constants)
    pub const fn memory_address(&self, fp: usize) -> Result<usize, RunnerError> {
        match self {
            Self::MemoryAfterFp { offset } => match fp.checked_add(*offset) {
                Some(addr) => Ok(addr),
                None => Err(RunnerError::AddressOverflow),
            },
            Self::FpRelative { .. } => Err(RunnerError::NotAPointer),
            Self::Constant(_) => Err(RunnerError::NotAPointer),
        }
    }

    /// Convert to MemOrConstant, panicking if FpRelative
    pub fn as_mem_or_constant(&self) -> MemOrConstant {
        match self {
            Self::MemoryAfterFp { offset } => MemOrConstant::MemoryAfterFp { offset: *offset },
            Self::Constant(c) => MemOrConstant::Constant(*c),
            Self::FpRelative { .. } => panic!("Cannot convert FpRelative to MemOrConstant"),
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
