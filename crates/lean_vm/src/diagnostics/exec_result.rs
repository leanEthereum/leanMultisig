use crate::core::F;
use crate::diagnostics::profiler::MemoryProfile;
use crate::execution::Memory;
use crate::{N_TABLES, TableTrace};
use thiserror::Error;

#[derive(Debug)]
pub struct ExecutionResult {
    pub no_vec_runtime_memory: usize,
    pub public_memory_size: usize,
    pub memory: Memory,
    pub pcs: Vec<usize>,
    pub fps: Vec<usize>,
    pub traces: [TableTrace; N_TABLES],
    pub summary: String,
    pub memory_profile: Option<MemoryProfile>,
}
