use crate::{
    MIN_LOG_MEMORY_SIZE,
    core::{F, SourceLocation},
};
use std::fmt::{Debug, Display};

#[derive(Clone, PartialEq)]
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
    RangeCheckWithTooBigRange {
        location: SourceLocation,
        range: usize,
    },
    InvalidExtensionOp,
    ParallelSegmentFailed(usize, Box<RunnerError>),
}

pub type VMResult<T> = Result<T, RunnerError>;

impl Display for RunnerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OutOfMemory => write!(f, "out of memory"),
            Self::MemoryAlreadySet {
                address,
                prev_value,
                new_value,
            } => {
                write!(f, "memory already set at {address}: prev={prev_value}, new={new_value}")
            }
            Self::NotAPointer => write!(f, "not a pointer"),
            Self::DivByZero => write!(f, "division by zero"),
            Self::NotEqual(left, right) => write!(f, "not equal: {left} != {right}"),
            Self::UndefinedMemory(address) => write!(f, "undefined memory: {address}"),
            Self::PCOutOfBounds => write!(f, "pc out of bounds"),
            Self::DebugAssertFailed(message, location) => {
                write!(f, "debug assert failed: {message} at {location}")
            }
            Self::RangeCheckWithTooBigRange { location, range } => {
                write!(
                    f,
                    "range checks only support ranges up to 2^{}, got {}, at {}. (leanVM supports `x < 1`, `x < 2`, ..., `x < 2^{}`, but not `x < 2^{} + 1`, cf. section 2.6.3 `Range checks` of minimal_zkVM.pdf)",
                    MIN_LOG_MEMORY_SIZE, range, location, MIN_LOG_MEMORY_SIZE, MIN_LOG_MEMORY_SIZE
                )
            }
            Self::InvalidExtensionOp => write!(f, "invalid extension op"),
            Self::ParallelSegmentFailed(id, err) => {
                write!(f, "parallel segment {id} failed: {err}")
            }
        }
    }
}

impl Debug for RunnerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(self, f)
    }
}
