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
        shift: usize,
    },
}

/// Represents a value that can be a memory location, the `fp` register itself, or a constant.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MemOrFpOrConstant {
    /// A memory location specified by a positive offset from `fp`. Represents `m[fp + shift]`.
    MemoryAfterFp {
        /// The offset from `fp` where the memory location is located.
        shift: usize,
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
        shift: usize,
    },
    /// The value of the frame pointer (`fp`) register itself.
    Fp,
}
