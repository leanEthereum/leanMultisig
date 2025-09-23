//! VM error types and execution results

use crate::core::F;
use crate::execution::Memory;
use crate::witness::{
    WitnessDotProduct, WitnessMultilinearEval, WitnessPoseidon16, WitnessPoseidon24,
};
use thiserror::Error;

/// Errors that can occur during VM execution
#[derive(Debug, Clone, Error)]
pub enum RunnerError {
    #[error("Out of memory")]
    OutOfMemory,

    #[error("Memory already set")]
    MemoryAlreadySet,

    #[error("Not a pointer")]
    NotAPointer,

    #[error("Division by zero")]
    DivByZero,

    #[error("Computation invalid: {0} != {1}")]
    NotEqual(F, F),

    #[error("Undefined memory access")]
    UndefinedMemory,

    #[error("Program counter out of bounds")]
    PCOutOfBounds,

    #[error("Point for multilinear eval not padded with zeros")]
    MultilinearEvalPointNotPadded,
}

/// Result type for VM operations
pub type VMResult<T> = Result<T, RunnerError>;

/// Execution result containing outputs and execution data
#[derive(Debug)]
pub struct ExecutionResult {
    pub no_vec_runtime_memory: usize,
    pub public_memory_size: usize,
    pub memory: Memory,
    pub pcs: Vec<usize>,
    pub fps: Vec<usize>,
    pub poseidons_16: Vec<WitnessPoseidon16>,
    pub poseidons_24: Vec<WitnessPoseidon24>,
    pub dot_products: Vec<WitnessDotProduct>,
    pub multilinear_evals: Vec<WitnessMultilinearEval>,
}

impl ExecutionResult {
    /// Check if execution was successful
    ///
    /// TODO: placeholder for now.
    pub fn is_success(&self) -> bool {
        true
    }
}
