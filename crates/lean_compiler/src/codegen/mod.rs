//! Code generation module for compiling simplified AST to intermediate bytecode.

pub mod compiler;
pub mod function;
pub mod instruction;
pub mod memory;
pub mod validation;

pub use compiler::Compiler;
pub use function::compile_function;
pub use instruction::compile_lines;
