use std::fmt::Debug;

use p3_field::PrimeField64;
use thiserror::Error;

use super::math::MathError;
use crate::memory::{address::MemoryAddress, val::MemoryValue};

#[derive(Debug, Eq, PartialEq, Error)]
pub enum MemoryError<F>
where
    F: PrimeField64,
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
    Math(#[from] MathError<F>),

    /// Error when a memory value is expected to be an integer, but it is an address to another memory location.
    #[error("Memory value should be an integer.")]
    ValueNotInteger,

    #[error("Memory at address {0:?} is uninitialized.")]
    UninitializedMemory(MemoryAddress),

    #[error("Memory address is expected but we got an integer.")]
    ExpectedMemoryAddress,

    #[error("Integer is expected but we got a memory address.")]
    ExpectedInteger,

    #[error("Operation failed: {} + {}, can't add two address values", 0.0, 0.1)]
    MemoryAddressAdd(Box<(MemoryAddress, MemoryAddress)>),

    #[error("Operation failed: {} * {}, can't multiply these two values", 0.0, 0.1)]
    InvalidMul(Box<(MemoryValue<F>, MemoryValue<F>)>),
}
