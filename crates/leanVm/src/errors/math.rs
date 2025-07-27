use thiserror::Error;

use crate::memory::address::MemoryAddress;

#[derive(Debug, Error, Eq, PartialEq)]
pub enum MathError {
    #[error("Operation failed: {} + {}, maximum offset value exceeded", 0.0, 0.1)]
    MemoryAddressAddUsizeOffsetExceeded(Box<(MemoryAddress, usize)>),
}
