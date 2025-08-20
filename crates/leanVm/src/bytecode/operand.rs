use p3_field::PrimeCharacteristicRing;

use crate::constant::F;

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
    #[must_use] pub const fn zero() -> Self {
        Self::Constant(F::ZERO)
    }

    /// Returns a constant operand with value `1`.
    #[must_use] pub const fn one() -> Self {
        Self::Constant(F::ONE)
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
