use crate::core::F;
use crate::diagnostics::profiler::MemoryProfile;
use crate::execution::Memory;
use crate::{TableTrace, error};
use thiserror::Error;

#[derive(Debug, Clone, Error)]
pub enum RunnerError {
    #[error("Out of memory")]
    OutOfMemory,

    #[error("Memory already set: m[{address}] = {prev_value} != {new_value}")]
    MemoryAlreadySet {
        address: usize,
        prev_value: F,
        new_value: F,
    },

    #[error("Not a pointer")]
    NotAPointer,

    #[error("Division by zero")]
    DivByZero,

    #[error("Computation invalid: {0} != {1}")]
    NotEqual(F, F),

    #[error("Undefined memory access: {0}")]
    UndefinedMemory(usize),

    #[error("Program counter out of bounds")]
    PCOutOfBounds,

    #[error("DebugAssert failed: {0} at line {1}")]
    DebugAssertFailed(String, usize),

    #[error("Invalid dot product")]
    InvalidDotProduct
}

pub type VMResult<T> = Result<T, RunnerError>;
