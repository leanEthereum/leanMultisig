//! Compiler module for IR compilation.

pub mod context;
pub mod helpers;
pub mod state;
pub mod traits;
pub mod types;

pub use context::CompileContext;
pub use helpers::{handle_const_malloc, mark_vars_as_declared, validate_vars_declared};
pub use state::Compiler;
pub use traits::{Compile, FindInternalVars};
pub use types::CompileResult;
