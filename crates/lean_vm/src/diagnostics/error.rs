use crate::core::{F, SourceLocation};

#[derive(Debug, Clone)]
pub enum RunnerError {
    OutOfMemory,
    MemoryAlreadySet {
        address: usize,
        prev_value: F,
        new_value: F,
    },
    NotAPointer,
    DivByZero,
    NotEqual(F, F),
    UndefinedMemory(usize),
    PCOutOfBounds,
    DebugAssertFailed(String, SourceLocation),
    InvalidExtensionOp,
}

pub type VMResult<T> = Result<T, RunnerError>;
