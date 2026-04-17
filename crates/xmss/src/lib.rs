#![cfg_attr(not(test), warn(unused_crate_dependencies))]
pub mod signers_cache;
mod wots;
use backend::Goldilocks;
pub use wots::*;
mod xmss;
pub use xmss::*;

pub(crate) const DIGEST_SIZE: usize = 4;

type F = Goldilocks;
type Digest = [F; DIGEST_SIZE];

// WOTS
pub const V: usize = 42;
pub const W: usize = 3;
pub const CHAIN_LENGTH: usize = 1 << W;
pub const NUM_CHAIN_HASHES: usize = 110;
pub const TARGET_SUM: usize = V * (CHAIN_LENGTH - 1) - NUM_CHAIN_HASHES;
pub const V_GRINDING: usize = 2;
pub const LOG_LIFETIME: usize = 32;
pub const RANDOMNESS_LEN_FE: usize = 4;
pub const MESSAGE_LEN_FE: usize = 4;
pub const TRUNCATED_MERKLE_ROOT_LEN_FE: usize = 3;

pub const SIG_SIZE_FE: usize = RANDOMNESS_LEN_FE + (V + LOG_LIFETIME) * DIGEST_SIZE;
