#![feature(map_try_insert)]

use std::collections::BTreeMap;

use lean_vm::*;

use crate::{
    a_simplify_lang::simplify_program, b_compile_intermediate::compile_to_intermediate_bytecode,
    c_compile_final::compile_to_low_level_bytecode, parser::parse_program,
};

mod a_simplify_lang;
mod b_compile_intermediate;
mod c_compile_final;
mod intermediate_bytecode;
mod lang;
mod parser;
mod precompiles;
pub use precompiles::PRECOMPILES;

pub fn compile_program(program: &str) -> (Bytecode, BTreeMap<usize, String>) {
    let (parsed_program, function_locations) = parse_program(program).unwrap();
    // println!("Parsed program: {}", parsed_program.to_string());
    let simple_program = simplify_program(parsed_program);
    // println!("Simplified program: {}", simple_program.to_string());
    let intermediate_bytecode = compile_to_intermediate_bytecode(simple_program).unwrap();
    // println!("Intermediate Bytecode:\n\n{}", intermediate_bytecode.to_string());
    let compiled = compile_to_low_level_bytecode(intermediate_bytecode).unwrap();
    println!("Function Locations: \n");
    for (loc, name) in function_locations.iter() {
        println!("{name}: {loc}");
    }
    println!("\n\nCompiled Program:\n\n{compiled}");
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
