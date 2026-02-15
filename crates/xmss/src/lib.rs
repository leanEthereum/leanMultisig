#![cfg_attr(not(test), warn(unused_crate_dependencies))]
use p3_koala_bear::KoalaBear;
pub mod signers_cache;
mod wots;
use utils::poseidon16_compress;
pub use wots::*;
mod xmss;
pub use xmss::*;

pub(crate) const DIGEST_SIZE: usize = 5;

type F = KoalaBear;
type Digest = [F; DIGEST_SIZE];
type PublicParam = [F; PUBLIC_PARAM_LEN_FE];
type Randomness = [F; RANDOMNESS_LEN_FE];

// WOTS
pub const V: usize = 40;
pub const W: usize = 3;
pub const CHAIN_LENGTH: usize = 1 << W;
pub const NUM_CHAIN_HASHES: usize = 120;
pub const TARGET_SUM: usize = V * (CHAIN_LENGTH - 1) - NUM_CHAIN_HASHES;
pub const V_GRINDING: usize = 3;
pub const LOG_LIFETIME: usize = 32;
pub const RANDOMNESS_LEN_FE: usize = 5;
pub const MESSAGE_LEN_FE: usize = 9;
pub const PUBLIC_PARAM_LEN_FE: usize = 3;

pub const SIG_SIZE_FE: usize = RANDOMNESS_LEN_FE + (V + LOG_LIFETIME) * DIGEST_SIZE;

pub type Poseidon16History = Vec<([F; 16], [F; 8])>;

fn poseidon16_compress_with_trace(a: [F; 8], b: [F; 8], poseidon_16_trace: &mut Vec<([F; 16], [F; 8])>) -> [F; 8] {
    let input: [F; 16] = [a, b].concat().try_into().unwrap();
    let output = poseidon16_compress(input);
    poseidon_16_trace.push((input, output));
    output
}
