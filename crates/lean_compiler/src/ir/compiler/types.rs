//! Type aliases and common types for compilation.

/// Result type for compilation operations.
pub type CompileResult<T = Vec<crate::ir::IntermediateInstruction>> = Result<T, String>;
