use std::collections::BTreeMap;

use lean_vm::*;

pub use compile::{compile_program_with_passes, compile_with_custom_passes};
pub use passes::{PassPipeline, PassPipelineBuilder};

mod analysis;
mod backend;
mod compile;
pub mod ir;
mod lang;
mod parser;
mod passes;
mod precompiles;
pub mod traits;
pub use precompiles::PRECOMPILES;

/// Compiles a program using the new pass architecture.
pub fn compile_program(program: &str) -> (Bytecode, BTreeMap<usize, String>) {
    compile_program_with_passes(program).unwrap_or_else(|e| panic!("Compilation error: {}", e))
}

pub fn compile_and_run(program: &str, public_input: &[F], private_input: &[F], profiler: bool) {
    let (bytecode, function_locations) = compile_program(program);
    execute_bytecode(
        &bytecode,
        public_input,
        private_input,
        program,
        &function_locations,
        profiler,
    );
}
