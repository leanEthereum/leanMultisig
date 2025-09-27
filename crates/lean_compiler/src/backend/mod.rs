//! Backend code generation module for compiling intermediate bytecode to low-level VM instructions.

pub mod compiler;
pub mod evaluation;

pub use compiler::compile_to_low_level_bytecode;
