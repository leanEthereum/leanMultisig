use thiserror::Error;

use crate::F;

#[derive(Debug, Clone, Error)]
pub enum RunnerError {
    #[error("Out of memory")]
    OutOfMemory,
    #[error("Memory already set")]
    MemoryAlreadySet,
    #[error("Not a pointer")]
    NotAPointer,
    #[error("Division by zero")]
    DivByZero,
    #[error("Computation invalid: {0} != {1}")]
    NotEqual(F, F),
    #[error("Undefined memory access")]
    UndefinedMemory,
    #[error("Program counter out of bounds")]
    PCOutOfBounds,
    #[error("Point for multilinear eval not padded with zeros")]
    MultilinearEvalPointNotPadded,
}
