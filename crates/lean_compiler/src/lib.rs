use lean_vm::*;

use crate::{
    a_simplify_lang::simplify_program, b_compile_intermediate::compile_to_intermediate_bytecode,
    c_compile_final::compile_to_low_level_bytecode, parser::parse_program,
};

mod a_simplify_lang;
mod b_compile_intermediate;
mod c_compile_final;
pub mod ir;
mod lang;
mod parser;

pub fn compile_program(program: String) -> Bytecode {
    let (parsed_program, function_locations) = parse_program(&program).unwrap();
    // println!("Parsed program: {}", parsed_program.to_string());
    let simple_program = simplify_program(parsed_program);
    // println!("Simplified program: {}", simple_program);
    let intermediate_bytecode = compile_to_intermediate_bytecode(simple_program).unwrap();
    // println!("Intermediate Bytecode:\n\n{}", intermediate_bytecode.to_string());

    // println!("Function Locations: \n");
    // for (loc, name) in function_locations.iter() {
    //     println!("{name}: {loc}");
    // }
    /* let compiled = */
    compile_to_low_level_bytecode(intermediate_bytecode, program, function_locations).unwrap() // ;
    // println!("\n\nCompiled Program:\n\n{compiled}");
    // compiled
}

pub fn compile_and_run(program: String, (public_input, private_input): (&[F], &[F]), profiler: bool) {
    let bytecode = compile_program(program);
    let summary = execute_bytecode(&bytecode, (public_input, private_input), profiler, &vec![], &vec![]).summary;
    println!("{summary}");
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
