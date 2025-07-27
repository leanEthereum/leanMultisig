use std::fmt::Debug;

use thiserror::Error;

use super::{math::MathError, memory::MemoryError};

#[derive(Debug, Error)]
pub enum VirtualMachineError<F>
where
    F: Debug,
{
    #[error(transparent)]
    Memory(#[from] MemoryError<F>),
    #[error(transparent)]
    Math(#[from] MathError),
}
