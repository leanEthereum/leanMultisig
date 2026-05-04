use crate::core::{F, SourceLocation};

#[derive(Debug, Clone, PartialEq)]
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
    InvalidSha256Input,
    ParallelSegmentFailed(usize, Box<RunnerError>),
}

pub type VMResult<T> = Result<T, RunnerError>;
