use std::{
    fmt,
    fmt::{Display, Formatter},
};

use p3_field::PrimeCharacteristicRing;

use crate::{F, Memory, RunnerError};

/// Represents a value that can either be a constant or a value from memory.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MemOrConstant {
    /// A constant value (a field element).
    Constant(F),
    /// A memory location specified by a positive offset from the frame pointer (`fp`).
    ///
    /// Represents the scalar value at `m[fp + shift]`.
    MemoryAfterFp {
        /// The offset from `fp` where the memory location is located.
        offset: usize,
    },
}

impl MemOrConstant {
    /// Converts the operand into its raw field representation for the trace.
    ///
    /// Returns a tuple `(operand, flag)` where:
    /// - `operand`: The field element representing the constant value or memory offset.
    /// - `flag`: A flag that is `1` for a constant and `0` for a memory access.
    #[must_use]
    pub fn to_field_and_flag(&self) -> (F, F) {
        match self {
            // If it's a constant, the flag is 1 and the value is the constant itself.
            Self::Constant(c) => (*c, F::ONE),
            // If it's a memory location, the flag is 0 and the value is the offset.
            Self::MemoryAfterFp { offset } => (F::from_usize(*offset), F::ZERO),
        }
    }

    /// Returns a constant operand with value `0`.
    #[must_use]
    pub const fn zero() -> Self {
        Self::Constant(F::ZERO)
    }

    /// Returns a constant operand with value `1`.
    #[must_use]
    pub const fn one() -> Self {
        Self::Constant(F::ONE)
    }
}

impl MemOrConstant {
    pub fn read_value(&self, memory: &Memory, fp: usize) -> Result<F, RunnerError> {
        match self {
            Self::Constant(c) => Ok(*c),
            Self::MemoryAfterFp { offset } => memory.get(fp + *offset),
        }
    }

    #[must_use]
    pub fn is_value_unknown(&self, memory: &Memory, fp: usize) -> bool {
        self.read_value(memory, fp).is_err()
    }

    pub const fn memory_address(&self, fp: usize) -> Result<usize, RunnerError> {
        match self {
            Self::Constant(_) => Err(RunnerError::NotAPointer),
            Self::MemoryAfterFp { offset } => Ok(fp + *offset),
        }
    }
}

impl Display for MemOrConstant {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Constant(c) => write!(f, "{c}"),
            Self::MemoryAfterFp { offset } => write!(f, "m[fp + {offset}]"),
        }
    }
}

/// Represents a value that can be a memory location, the `fp` register itself, or a constant.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MemOrFpOrConstant {
    /// A memory location specified by a positive offset from `fp`. Represents `m[fp + shift]`.
    MemoryAfterFp {
        /// The offset from `fp` where the memory location is located.
        offset: usize,
    },
    /// The value of the frame pointer (`fp`) register itself.
    Fp,
    /// A constant value (a field element).
    Constant(F),
}

impl MemOrFpOrConstant {
    pub fn read_value(&self, memory: &Memory, fp: usize) -> Result<F, RunnerError> {
        match self {
            Self::MemoryAfterFp { offset } => memory.get(fp + *offset),
            Self::Fp => Ok(F::from_usize(fp)),
            Self::Constant(c) => Ok(*c),
        }
    }

    #[must_use]
    pub fn is_value_unknown(&self, memory: &Memory, fp: usize) -> bool {
        self.read_value(memory, fp).is_err()
    }

    pub const fn memory_address(&self, fp: usize) -> Result<usize, RunnerError> {
        match self {
            Self::MemoryAfterFp { offset } => Ok(fp + *offset),
            Self::Fp | Self::Constant(_) => Err(RunnerError::NotAPointer),
        }
    }
}

impl Display for MemOrFpOrConstant {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::MemoryAfterFp { offset } => write!(f, "m[fp + {offset}]"),
            Self::Fp => f.write_str("fp"),
            Self::Constant(c) => write!(f, "{c}"),
        }
    }
}

/// Represents a value that is either a memory location or the `fp` register itself.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MemOrFp {
    /// A memory location specified by a positive offset from `fp`. Represents `m[fp + shift]`.
    MemoryAfterFp {
        /// The offset from `fp` where the memory location is located.
        offset: usize,
    },
    /// The value of the frame pointer (`fp`) register itself.
    Fp,
}

impl MemOrFp {
    /// Converts the operand into its raw field representation for the trace.
    ///
    /// Returns a tuple `(operand, flag)` where:
    /// - `operand`: The field element representing the memory offset (or 0 if `Fp`).
    /// - `flag`: A flag that is `1` for the `Fp` register and `0` for a memory access.
    #[must_use]
    pub fn to_field_and_flag(&self) -> (F, F) {
        match self {
            // If it's the frame pointer, the flag is 1 and the operand value is 0.
            Self::Fp => (F::ZERO, F::ONE),
            // If it's a memory location, the flag is 0 and the value is the offset.
            Self::MemoryAfterFp { offset } => (F::from_usize(*offset), F::ZERO),
        }
    }
}

impl MemOrFp {
    pub fn read_value(&self, memory: &Memory, fp: usize) -> Result<F, RunnerError> {
        match self {
            Self::MemoryAfterFp { offset } => memory.get(fp + *offset),
            Self::Fp => Ok(F::from_usize(fp)),
        }
    }

    #[must_use]
    pub fn is_value_unknown(&self, memory: &Memory, fp: usize) -> bool {
        self.read_value(memory, fp).is_err()
    }

    pub const fn memory_address(&self, fp: usize) -> Result<usize, RunnerError> {
        match self {
            Self::MemoryAfterFp { offset } => Ok(fp + *offset),
            Self::Fp => Err(RunnerError::NotAPointer),
        }
    }
}

impl Display for MemOrFp {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::MemoryAfterFp { offset } => write!(f, "m[fp + {offset}]"),
            Self::Fp => f.write_str("fp"),
        }
    }
}
