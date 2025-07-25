use std::fmt::Debug;

use thiserror::Error;

use super::{address::MemoryAddress, val::MemoryValue};
use crate::types::math_errors::MathError;

#[derive(Debug, Eq, PartialEq, Error)]
pub enum MemoryError<F>
where
    F: Debug,
{
    /// Error for when an operation targets a memory segment that has not been allocated.
    #[error(
        "Memory access out of bounds: cannot access segment {}, as only {} segments are allocated.",
        0.0,
        0.1
    )]
    UnallocatedSegment(Box<(usize, usize)>),

    /// Error for attempting to overwrite an existing, different value in a memory cell, violating write-once consistency.
    #[error(
        "Write-once violation at address {:?}: cannot overwrite existing value '{:?}' with new value '{:?}'.",
        0.0,
        0.1,
        0.2
    )]
    InconsistentMemory(Box<(MemoryAddress, MemoryValue<F>, MemoryValue<F>)>),

    /// Error for when a memory operation would exceed the maximum capacity of a segment vector.
    #[error(
        "Memory overflow: the requested memory address is too large and exceeds the machine's capacity."
    )]
    VecCapacityExceeded,

    /// Error related to mathematical operations.
    #[error(transparent)]
    Math(#[from] MathError),
}
