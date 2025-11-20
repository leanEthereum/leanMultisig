use crate::core::F;
use crate::diagnostics::profiler::MemoryProfile;
use crate::execution::Memory;
use crate::{N_PRECOMPILES, PrecompileTrace, WitnessMultilinearEval};
use thiserror::Error;


#[derive(Debug)]
pub struct ExecutionResult {
    pub no_vec_runtime_memory: usize,
    pub public_memory_size: usize,
    pub memory: Memory,
    pub pcs: Vec<usize>,
    pub fps: Vec<usize>,
    pub precompile_traces: [PrecompileTrace; N_PRECOMPILES],
    pub multilinear_evals_witness: Vec<WitnessMultilinearEval>,
    pub summary: String,
    pub memory_profile: Option<MemoryProfile>,
}
