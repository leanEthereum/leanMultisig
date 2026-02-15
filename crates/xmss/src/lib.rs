#![cfg_attr(not(test), warn(unused_crate_dependencies))]
use p3_koala_bear::KoalaBear;
pub mod signers_cache;
mod wots;
use utils::poseidon16_compress;
pub use wots::*;
mod xmss;
pub use xmss::*;

pub(crate) const DIGEST_SIZE: usize = 5;
pub(crate) const TWEAK_LEN: usize = 2;

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

// Tweak: domain separation within each hash.
pub(crate) const TWEAK_TYPE_CHAIN: usize = 0;
pub(crate) const TWEAK_TYPE_WOTS_PK: usize = 1;
pub(crate) const TWEAK_TYPE_MERKLE: usize = 2;
pub(crate) const TWEAK_TYPE_ENCODING: usize = 3;

use multilinear_toolkit::prelude::*;

/// index = slot or node_index in Merkle tree
pub(crate) fn make_tweak(tweak_type: usize, sub_position: usize, index: u32) -> [F; TWEAK_LEN] {
    assert!(tweak_type < 4);
    assert!(sub_position < 1 << 10);
    let index_lo = (index & 0xFFFF) as usize;
    let index_hi = (index >> 16) as usize;
    [
        F::from_usize((tweak_type << 26) + (index_hi << 10) + sub_position),
        F::from_usize(index_lo),
    ]
}

/// [public_param(3) | data(5)]
pub(crate) fn build_left(public_param: &PublicParam, data: &Digest) -> [F; 8] {
    let mut left = [F::default(); 8];
    left[..PUBLIC_PARAM_LEN_FE].copy_from_slice(public_param);
    left[PUBLIC_PARAM_LEN_FE..].copy_from_slice(data);
    left
}

/// [0 | tweak(2) | data(5)]
pub(crate) fn build_right(tweak: [F; TWEAK_LEN], data: &Digest) -> [F; 8] {
    let mut right = [F::default(); 8];
    right[1..1 + TWEAK_LEN].copy_from_slice(&tweak);
    right[1 + TWEAK_LEN..].copy_from_slice(data);
    right
}

fn poseidon16_compress_with_trace(a: [F; 8], b: [F; 8], poseidon_16_trace: &mut Vec<([F; 16], [F; 8])>) -> [F; 8] {
    let input: [F; 16] = [a, b].concat().try_into().unwrap();
    let output = poseidon16_compress(input);
    poseidon_16_trace.push((input, output));
    output
}
