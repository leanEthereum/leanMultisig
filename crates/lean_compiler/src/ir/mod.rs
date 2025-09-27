//! Intermediate Representation (IR) for the Lean compiler.

pub mod bytecode;
pub mod conversion;
pub mod instruction;
pub mod operation;
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
pub use types::{
    ArrayManager, ConstMalloc, Counters, SimpleFunction, SimpleLine, SimpleProgram,
    VarOrConstMallocAccess,
};

// Re-export utilities
pub use utilities::replace_vars_by_const_in_lines;
