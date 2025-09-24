//! VM operand types and addressing modes

pub mod mem_or_constant;
pub mod mem_or_fp;
pub mod mem_or_fp_or_constant;

pub use mem_or_constant::*;
pub use mem_or_fp::*;
pub use mem_or_fp_or_constant::*;
