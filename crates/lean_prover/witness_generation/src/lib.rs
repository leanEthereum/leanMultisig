#![cfg_attr(not(test), allow(unused_crate_dependencies))]

mod execution_trace;
mod instruction_encoder;

pub use execution_trace::*;
pub use instruction_encoder::*;

mod poseidon_tables;
pub use poseidon_tables::*;

// Zero padding will be added to each at least, if this minimum is not reached
// (ensuring AIR / GKR work fine, with SIMD, without too much edge cases)
// Long term, we should find a more elegant solution.
pub const LOG_MIN_POSEIDONS_16: usize = 8;
pub const LOG_MIN_POSEIDONS_24: usize = 8;
pub const LOG_MIN_DOT_PRODUCT_ROWS: usize = 8;
