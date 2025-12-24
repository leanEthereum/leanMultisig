use std::collections::BTreeMap;

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

#[derive(Debug, Clone)]
pub enum ProgramSource {
    Raw(String),
    Filepath(String),
}

impl ProgramSource {
    pub fn get_content(&self, flags: &CompilationFlags) -> Result<String, std::io::Error> {
        match self {
            ProgramSource::Raw(src) => {
                let mut result = src.clone();
                for (key, value) in flags.replacements.iter() {
                    result = result.replace(key, value);
                }
                Ok(result)
            }
            ProgramSource::Filepath(fp) => {
                let mut result = std::fs::read_to_string(fp)?;
                for (key, value) in flags.replacements.iter() {
                    result = result.replace(key, value);
                }
                Ok(result)
            }
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct CompilationFlags {
    /// useful for placeholder replacements in source code
    pub replacements: BTreeMap<String, String>,
}

pub fn compile_program_with_flags(input: &ProgramSource, flags: CompilationFlags) -> Bytecode {
    let parsed_program = parse_program(input, flags).unwrap();
    // println!("Parsed program: {}", parsed_program.to_string());
    let function_locations = parsed_program.function_locations.clone();
    let source_code = parsed_program.source_code.clone();
    let filepaths = parsed_program.filepaths.clone();
    let simple_program = simplify_program(parsed_program);
    // println!("Simplified program: {}", simple_program);
    let intermediate_bytecode = compile_to_intermediate_bytecode(simple_program).unwrap();
    // println!("Intermediate Bytecode:\n\n{}", intermediate_bytecode.to_string());

    // println!("Function Locations: \n");
    // for (loc, name) in function_locations.iter() {
    //     println!("{name}: {loc}");
    // }
    /* let compiled = */
    compile_to_low_level_bytecode(intermediate_bytecode, function_locations, source_code, filepaths).unwrap() // ;
    // println!("\n\nCompiled Program:\n\n{compiled}");
    // compiled
}

pub fn compile_program(input: &ProgramSource) -> Bytecode {
    compile_program_with_flags(input, CompilationFlags::default())
}

pub fn compile_and_run(
    source: &ProgramSource,
    (public_input, private_input): (&[F], &[F]),
    no_vec_runtime_memory: usize, // size of the "non-vectorized" runtime memory
    profiler: bool,
) {
    let bytecode = compile_program(source);
    let summary = execute_bytecode(
        &bytecode,
        (public_input, private_input),
        no_vec_runtime_memory,
        profiler,
        (&vec![], &vec![]),
        Default::default(),
    )
    .summary;
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
