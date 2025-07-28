use p3_field::PrimeField64;
use thiserror::Error;

use crate::memory::address::MemoryAddress;

#[derive(Debug, Error, Eq, PartialEq)]
pub enum MathError<F>
where
    F: PrimeField64,
{
    #[error("Operation failed: {} + {}, maximum offset value exceeded", 0.0, 0.1)]
    MemoryAddressAddUsizeOffsetExceeded(Box<(MemoryAddress, usize)>),
    #[error("Operation failed: {} + {}, maximum offset value exceeded", 0.0, 0.1)]
    MemoryAddressAddFieldOffsetExceeded(Box<(MemoryAddress, F)>),
    #[error("Division by zero")]
    DivisionByZero,
}
