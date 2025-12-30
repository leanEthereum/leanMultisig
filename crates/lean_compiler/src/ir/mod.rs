//! Intermediate Representation (IR) for the Lean compiler.

pub mod bytecode;
pub mod instruction;
pub mod operation;
pub mod value;

pub use bytecode::{IntermediateBytecode, MatchBlock};
pub use instruction::IntermediateInstruction;
pub use operation::HighLevelOperation;
pub use value::IntermediateValue;
