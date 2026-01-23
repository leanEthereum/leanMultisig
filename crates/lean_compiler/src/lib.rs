use std::collections::BTreeMap;
use std::fmt;

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

pub use parser::{ParseError, RESERVED_FUNCTION_NAMES};

pub use lean_vm::RunnerError;

#[derive(Debug)]
pub enum CompileError {
    Parse(ParseError),
    Compile(String),
    Io(std::io::Error),
}

impl fmt::Display for CompileError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Parse(e) => write!(f, "{e}"),
            Self::Compile(e) => write!(f, "Compile error: {e}"),
            Self::Io(e) => write!(f, "IO error: {e}"),
        }
    }
}

impl std::error::Error for CompileError {}

impl From<ParseError> for CompileError {
    fn from(e: ParseError) -> Self {
        Self::Parse(e)
    }
}

impl From<String> for CompileError {
    fn from(e: String) -> Self {
        Self::Compile(e)
    }
}

impl From<std::io::Error> for CompileError {
    fn from(e: std::io::Error) -> Self {
        Self::Io(e)
    }
}

/// Error type for compile and run operations
#[derive(Debug)]
pub enum Error {
    Compile(CompileError),
    Runtime(RunnerError),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Compile(e) => write!(f, "{e}"),
            Self::Runtime(e) => write!(f, "Runtime error: {e}"),
        }
    }
}

impl std::error::Error for Error {}

impl From<CompileError> for Error {
    fn from(e: CompileError) -> Self {
        Self::Compile(e)
    }
}

impl From<RunnerError> for Error {
    fn from(e: RunnerError) -> Self {
        Self::Runtime(e)
    }
}

#[derive(Debug, Clone)]
pub enum ProgramSource {
    Raw(String),
    Filepath(String),
}

impl ProgramSource {
    pub fn get_content(&self, flags: &CompilationFlags) -> Result<String, String> {
        match self {
            ProgramSource::Raw(src) => {
                let mut result = src.clone();
                for (key, value) in flags.replacements.iter() {
                    result = result.replace(key, value);
                }
                Ok(result)
            }
            ProgramSource::Filepath(fp) => {
                let mut result = std::fs::read_to_string(fp).map_err(|e| format!("Failed to read file {fp}: {e}"))?;
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

pub fn try_compile_program_with_flags(
    input: &ProgramSource,
    flags: CompilationFlags,
) -> Result<Bytecode, CompileError> {
    let parsed_program = parse_program(input, flags)?;
    let function_locations = parsed_program.function_locations.clone();
    let source_code = parsed_program.source_code.clone();
    let filepaths = parsed_program.filepaths.clone();
    let simple_program = simplify_program(parsed_program)?;
    let intermediate_bytecode = compile_to_intermediate_bytecode(simple_program)?;
    let bytecode = compile_to_low_level_bytecode(intermediate_bytecode, function_locations, source_code, filepaths)?;
    Ok(bytecode)
}

pub fn compile_program_with_flags(input: &ProgramSource, flags: CompilationFlags) -> Bytecode {
    try_compile_program_with_flags(input, flags).unwrap()
}

pub fn try_compile_program(input: &ProgramSource) -> Result<Bytecode, CompileError> {
    try_compile_program_with_flags(input, Default::default())
}

pub fn compile_program(input: &ProgramSource) -> Bytecode {
    try_compile_program(input).unwrap()
}

pub fn try_compile_and_run(
    input: &ProgramSource,
    (public_input, private_input): (&[F], &[F]),
    profiler: bool,
) -> Result<String, Error> {
    let bytecode = try_compile_program(input)?;
    let result = try_execute_bytecode(&bytecode, (public_input, private_input), profiler, &vec![])?;
    Ok(result.summary)
}

pub fn compile_and_run(input: &ProgramSource, (public_input, private_input): (&[F], &[F]), profiler: bool) {
    let summary = try_compile_and_run(input, (public_input, private_input), profiler).unwrap();
    println!("{summary}");
}
