//! Code generation module for compiling simplified AST to intermediate bytecode.

pub mod compiler;
pub mod function;
pub mod memory;

pub use compiler::Compiler;
pub use function::compile_function;
