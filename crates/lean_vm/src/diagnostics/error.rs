use std::fmt;

use crate::core::{F, SourceLocation};
use crate::diagnostics::profiler::MemoryProfile;
use crate::execution::Memory;
use crate::{TableTrace, error};

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
    InvalidDotProduct,
}

pub type VMResult<T> = Result<T, RunnerError>;
