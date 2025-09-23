//! Memory or frame pointer operand type

use crate::core::F;
use crate::diagnostics::RunnerError;
use crate::execution::Memory;
use p3_field::PrimeCharacteristicRing;
use std::fmt::{Display, Formatter};

/// Memory or frame pointer operand - represents a value from memory or the frame pointer itself
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MemOrFp {
    /// Memory address relative to frame pointer: m[fp + offset]
    MemoryAfterFp {
        /// Offset from frame pointer
        offset: usize,
    },
    /// The frame pointer value itself
    Fp,
}

impl MemOrFp {
    /// Read the value from memory or return the frame pointer
    pub fn read_value(&self, memory: &Memory, fp: usize) -> Result<F, RunnerError> {
        match self {
            Self::MemoryAfterFp { offset } => memory.get(fp + *offset),
            Self::Fp => Ok(F::from_usize(fp)),
        }
    }

    /// Check if the value is unknown (would error when read)
    pub fn is_value_unknown(&self, memory: &Memory, fp: usize) -> bool {
        self.read_value(memory, fp).is_err()
    }

    /// Get the memory address (returns error for Fp)
    pub const fn memory_address(&self, fp: usize) -> Result<usize, RunnerError> {
        match self {
            Self::MemoryAfterFp { offset } => Ok(fp + *offset),
            Self::Fp => Err(RunnerError::NotAPointer),
        }
    }
}

impl Display for MemOrFp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MemoryAfterFp { offset } => write!(f, "m[fp + {offset}]"),
            Self::Fp => write!(f, "fp"),
        }
    }
}
