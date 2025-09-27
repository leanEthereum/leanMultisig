//! Intermediate Representation (IR) for the Lean compiler.

pub mod bytecode;
pub mod compiler;
pub mod conversion;
pub mod instruction;
pub mod operation;
pub mod simple_function;
pub mod simple_line;
pub mod types;
pub mod unroll;
pub mod utilities;
pub mod value;

// Low-level IR exports (bytecode generation)
pub use bytecode::IntermediateBytecode;
pub use instruction::IntermediateInstruction;
pub use operation::HighLevelOperation;
pub use value::{IntermediaryMemOrFpOrConstant, IntermediateValue};

// High-level IR exports (AST to IR)
pub use simple_function::SimpleFunction;
pub use simple_line::SimpleLine;
pub use types::{ArrayManager, ConstMalloc, Counters, SimpleProgram, VarOrConstMallocAccess};

// New trait-based compilation exports
pub use compiler::{Compile, CompileContext, CompileResult, FindInternalVars};
