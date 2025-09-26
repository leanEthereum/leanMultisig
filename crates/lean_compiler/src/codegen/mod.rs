/// Code generation module for compiling simplified AST to intermediate bytecode.
///
/// This module provides clean, modular components for compiling high-level
/// language constructs into low-level intermediate representation, following
/// best practices from LLVM, GCC, and other production compilers.
pub mod compiler;
pub mod function;
pub mod instruction;
pub mod memory;
pub mod validation;

pub use compiler::Compiler;
pub use function::compile_function;
pub use instruction::compile_lines;