use std::fmt::Debug;

use p3_field::PrimeField64;
use thiserror::Error;

use super::{math::MathError, memory::MemoryError};
use crate::memory::val::MemoryValue;

#[derive(Debug, Error)]
pub enum VirtualMachineError<F>
where
    F: PrimeField64,
{
    #[error(transparent)]
    Memory(#[from] MemoryError<F>),
    #[error(transparent)]
    Math(#[from] MathError<F>),
    #[error(
        "Assertion failed: computed value '{:?}' != expected value '{:?}'.",
        computed,
        expected
    )]
    AssertEqFailed {
        computed: MemoryValue<F>,
        expected: MemoryValue<F>,
    },
    #[error("Too many unknown operands.")]
    TooManyUnknownOperands,
}
