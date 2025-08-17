use super::Bytecode;
use crate::{
    constant::F,
    memory::{address::MemoryAddress, manager::MemoryManager},
};

/// Represents a program to be executed by the zkVM.
#[derive(Debug, Clone, Default)]
pub struct Program {
    /// The compiled instructions and hints for the program.
    pub bytecode: Bytecode,
    /// The public inputs for this specific execution.
    pub public_input: Vec<F>,
    /// The private (witness) inputs for this specific execution.
    pub private_input: Vec<F>,
}

/// Represents the results of a successful program execution.
#[derive(Debug)]
pub struct ExecutionResult {
    /// The size of the public memory region.
    pub public_memory_size: usize,
    /// The final state of the memory manager.
    pub memory_manager: MemoryManager,
    /// The execution trace of the program counter (pc) values.
    ///
    /// TODO: in the future, not sure we need this.
    pub pcs: Vec<MemoryAddress>,
    /// The execution trace of the frame pointer (fp) values.
    ///
    /// TODO: in the future, not sure we need this.
    pub fps: Vec<MemoryAddress>,
}

/// An helper struct to hold the results of a single execution pass.
#[derive(Debug)]
pub struct ExecutionPassResult {
    /// The result of the execution.
    pub result: ExecutionResult,
    /// The initial allocation pointers.
    pub initial_ap: MemoryAddress,
    /// The initial allocation pointers for vectorized memory.
    pub initial_ap_vec: MemoryAddress,
}
