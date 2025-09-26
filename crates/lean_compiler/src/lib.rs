use std::collections::BTreeMap;

use lean_vm::*;

use crate::{
    c_compile_final::compile_to_low_level_bytecode, codegen::Compiler, parser::parse_program,
    simplify::simplify_program,
};

mod c_compile_final;
pub mod codegen;
pub mod ir;
mod lang;
mod parser;
mod precompiles;
mod simplify;
pub use precompiles::PRECOMPILES;

/// Compiles a program.
pub fn compile_program(program: &str) -> (Bytecode, BTreeMap<usize, String>) {
    let (parsed_program, function_locations) =
        parse_program(program).unwrap_or_else(|e| panic!("Parse error: {}", e));

    let simple_program = simplify_program(parsed_program);

    let mut compiler = Compiler::new();
    let intermediate_bytecode = compiler
        .compile_program(simple_program)
        .unwrap_or_else(|e| panic!("Compilation error: {}", e));

    let compiled = compile_to_low_level_bytecode(intermediate_bytecode)
        .unwrap_or_else(|e| panic!("Low-level compilation error: {}", e));

    (compiled, function_locations)
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

#[derive(Debug, Clone, Default)]
struct Counter(usize);

impl Counter {
    const fn next(&mut self) -> usize {
        let val = self.0;
        self.0 += 1;
        val
    }

    const fn new() -> Self {
        Self(0)
    }
}
