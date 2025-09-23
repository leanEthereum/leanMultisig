//! Instruction Set Architecture (ISA) definitions

pub mod bytecode;
pub mod instruction;
pub mod operation;
pub mod operands;

pub use bytecode::*;
pub use instruction::*;
pub use operation::*;
pub use operands::*;

/// String label for bytecode locations
pub type Label = String;