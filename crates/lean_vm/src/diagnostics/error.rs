use crate::core::F;
use crate::execution::Memory;
use crate::witness::{
    WitnessDotProduct, WitnessMultilinearEval, WitnessPoseidon16, WitnessPoseidon24,
};
use thiserror::Error;

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

    #[error("Undefined memory access: {0}")]
    UndefinedMemory(usize),

    #[error("Program counter out of bounds")]
    PCOutOfBounds,

    #[error("Point for multilinear eval not padded with zeros")]
    MultilinearEvalPointNotPadded,
}

pub type VMResult<T> = Result<T, RunnerError>;

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
