use std::collections::BTreeMap;

use lean_vm::*;

pub use crate::{
    a_simplify_lang::{SimpleLine, simplify_program},
    b_compile_intermediate::compile_to_intermediate_bytecode,
    c_compile_to_low_level_bytecode::compile_to_low_level_bytecode,
    d_compile_range_checks::compile_range_checks,
};

pub use {
    lang::{Expression, Line, SimpleExpr},
    parser::parse_program,
};

mod a_simplify_lang;
mod b_compile_intermediate;
mod c_compile_to_low_level_bytecode;
mod d_compile_range_checks;
mod ir;
mod lang;
mod parser;
mod precompiles;
pub use precompiles::PRECOMPILES;

pub fn compile_program(
    program: &str,
    public_input: &[F],
    private_input: &[F],
) -> (Bytecode, BTreeMap<usize, String>) {
    let (parsed_program, function_locations) = parse_program(program).unwrap();
    let simple_program = simplify_program(parsed_program);
    let intermediate_bytecode = compile_to_intermediate_bytecode(simple_program).unwrap();
    let mut compiled = compile_to_low_level_bytecode(intermediate_bytecode).unwrap();

    // Check if range checks exist - if so, compile them
    if compiled
        .hints
        .values()
        .any(|hints| hints.iter().any(|h| matches!(h, Hint::RangeCheck { .. })))
    {
        // First execution to get execution trace for range check compilation
        let mut std_out = String::new();
        let mut instruction_history = ExecutionHistory::default();
        let first_exec = execute_bytecode_helper(
            &compiled,
            public_input,
            private_input,
            MAX_RUNNER_MEMORY_SIZE / 2,
            &mut std_out,
            &mut instruction_history,
            false,
            &function_locations,
        )
        .unwrap();

        // Compile range checks using the execution result
        compiled = compile_range_checks(&first_exec, &compiled).unwrap();
    }

    (compiled, function_locations)
}

pub fn compile_and_run(
    program: &str,
    public_input: &[F],
    private_input: &[F],
    no_vec_runtime_memory: usize, // size of the "non-vectorized" runtime memory
    profiler: bool,
) {
    let (bytecode, function_locations) = compile_program(program, public_input, private_input);
    execute_bytecode(
        &bytecode,
        public_input,
        private_input,
        program,
        &function_locations,
        no_vec_runtime_memory,
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
