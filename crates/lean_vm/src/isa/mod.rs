//! Instruction Set Architecture (ISA) definitions

pub mod bytecode;
pub mod instruction;
pub mod operands;
pub mod operation;

pub use bytecode::*;
pub use instruction::*;
pub use operands::*;
pub use operation::*;

/// String label for bytecode locations
pub type Label = String;
