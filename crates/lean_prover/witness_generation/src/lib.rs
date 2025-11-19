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
pub const MIN_LOG_N_ROWS_PER_TABLE: usize = 8;
pub const MIN_N_ROWS_PER_TABLE: usize = 1 << MIN_LOG_N_ROWS_PER_TABLE;
