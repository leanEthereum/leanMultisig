use p3_koala_bear::{KoalaBear, QuinticExtensionFieldKB};

mod bytecode;
mod error;
mod memory;
mod profiler;
mod runner;
mod stack_trace;
pub use bytecode::*;
pub use error::*;
pub use memory::*;
pub use runner::*;

pub type LocationInSourceCode = usize;

pub const DIMENSION: usize = 5;
pub const LOG_VECTOR_LEN: usize = 3;
pub const VECTOR_LEN: usize = 1 << LOG_VECTOR_LEN;
pub type F = KoalaBear;
pub type EF = QuinticExtensionFieldKB;

pub const ZERO_VEC_PTR: usize = 0; // convention (vectorized pointer of size 2, pointing to 16 zeros)
pub const ONE_VEC_PTR: usize = 2; // convention (vectorized pointer of size 1, pointing to 10000000)
pub const POSEIDON_16_NULL_HASH_PTR: usize = 3; // convention (vectorized pointer of size 2, = the 16 elements of poseidon_16(0))
pub const POSEIDON_24_NULL_HASH_PTR: usize = 5; // convention (vectorized pointer of size 1, = the last 8 elements of poseidon_24(0))
pub const PUBLIC_INPUT_START: usize = 6 * 8; // normal pointer
