use std::fmt::Debug;

use thiserror::Error;

use super::{math::MathError, memory::MemoryError};
use crate::memory::val::MemoryValue;

#[derive(Debug, Error)]
pub enum VirtualMachineError {
    #[error(transparent)]
    Memory(#[from] MemoryError),
    #[error(transparent)]
    Math(#[from] MathError),
    #[error(
        "Assertion failed: computed value '{:?}' != expected value '{:?}'.",
        computed,
        expected
    )]
    AssertEqFailed {
        computed: MemoryValue,
        expected: MemoryValue,
    },
    #[error("Too many unknown operands.")]
    TooManyUnknownOperands,
    #[error("Program counter (pc) is out of bounds.")]
    PCOutOfBounds,
}
