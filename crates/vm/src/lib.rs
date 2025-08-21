use p3_field::extension::BinomialExtensionField;
use p3_koala_bear::KoalaBear;

mod bytecode;
mod runner;
pub use bytecode::*;
pub use runner::*;

pub const DIMENSION: usize = 8;
pub type F = KoalaBear;
pub type EF = BinomialExtensionField<F, DIMENSION>;

pub const ZERO_VEC_PTR: usize = 0; // convention (vectorized pointer of size 1, pointing to 8 zeros)
pub const POSEIDON_16_NULL_HASH_PTR: usize = 2; // convention (vectorized pointer of size 2, = the 16 elements of poseidon_16(0))
pub const POSEIDON_24_NULL_HASH_PTR: usize = 4; // convention (vectorized pointer of size 1, = the last 8 elements of poseidon_24(0))
pub const PUBLIC_INPUT_START: usize = 5 * 8; // normal pointer
