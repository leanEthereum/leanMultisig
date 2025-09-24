//! Lean VM - A minimal virtual machine implementation

pub mod core;
pub mod diagnostics;
pub mod execution;
pub mod isa;
pub mod witness;

pub use core::*;
pub use diagnostics::*;
pub use execution::*;
pub use isa::*;
pub use witness::*;

/// Main execution entry point for the VM
pub fn execute_bytecode(
    bytecode: &Bytecode,
    public_input: &[F],
    private_input: &[F],
    source_code: &str,
    function_locations: &std::collections::BTreeMap<usize, String>,
    profiler: bool,
) -> ExecutionResult {
    execution::execute_bytecode_impl(
        bytecode,
        public_input,
        private_input,
        source_code,
        function_locations,
        profiler,
    )
}
