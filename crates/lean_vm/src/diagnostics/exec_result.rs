use crate::core::F;
use crate::diagnostics::profiler::MemoryProfile;
use crate::execution::Memory;
use crate::{PrecompileTrace, WitnessMultilinearEval};
use thiserror::Error;


#[derive(Debug)]
pub struct ExecutionResult {
    pub no_vec_runtime_memory: usize,
    pub public_memory_size: usize,
    pub memory: Memory,
    pub pcs: Vec<usize>,
    pub fps: Vec<usize>,
    pub poseidons_16: PrecompileTrace,
    pub poseidons_24: PrecompileTrace,
    pub dot_products: PrecompileTrace,
    pub multilinear_evals: PrecompileTrace,
    pub multilinear_evals_witness: Vec<WitnessMultilinearEval>,
    pub summary: String,
    pub memory_profile: Option<MemoryProfile>,
}
