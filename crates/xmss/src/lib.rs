#![cfg_attr(not(test), warn(unused_crate_dependencies))]
pub mod signers_cache;
mod wots;
use backend::KoalaBear;
pub use wots::*;
mod xmss;
pub use xmss::*;

pub const DIGEST_SIZE: usize = 4;
pub(crate) const TWEAK_LEN: usize = 2;

type F = KoalaBear;
type Digest = [F; DIGEST_SIZE];
type PublicParam = [F; PUBLIC_PARAM_LEN_FE];
type Randomness = [F; RANDOMNESS_LEN_FE];

// WOTS
pub const V: usize = 42;
pub const W: usize = 3;
pub const CHAIN_LENGTH: usize = 1 << W;
pub const NUM_CHAIN_HASHES: usize = 110;
pub const TARGET_SUM: usize = V * (CHAIN_LENGTH - 1) - NUM_CHAIN_HASHES;
pub const V_GRINDING: usize = 2;
pub const LOG_LIFETIME: usize = 32;
pub const RANDOMNESS_LEN_FE: usize = 5;
pub const MESSAGE_LEN_FE: usize = 9;
pub const PUBLIC_PARAM_LEN_FE: usize = 4;
/// Length of the non-data prefix in either Poseidon input. Both inputs reserve the
/// first `INPUT_PREFIX_LEN` field elements for metadata (tweak/zeros on the left,
/// public_param on the right) and place the 4-element data digest right after it.
pub const INPUT_PREFIX_LEN: usize = 8 - DIGEST_SIZE; // = 4
pub const PUB_KEY_FLAT_SIZE: usize = DIGEST_SIZE + PUBLIC_PARAM_LEN_FE; // = 9

const _: () = assert!(INPUT_PREFIX_LEN + DIGEST_SIZE == 8);
// Left layout (with tweak): [tweak(2) | zeros(2) | data(DIGEST_SIZE)]
const _: () = assert!(TWEAK_LEN + 2 + DIGEST_SIZE == 8);

pub const SIG_SIZE_FE: usize = RANDOMNESS_LEN_FE + (V + LOG_LIFETIME) * DIGEST_SIZE;

// Tweak: domain separation within each hash.
pub(crate) const TWEAK_TYPE_CHAIN: usize = 0;
pub(crate) const TWEAK_TYPE_WOTS_PK: usize = 1;
pub(crate) const TWEAK_TYPE_MERKLE: usize = 2;
pub(crate) const TWEAK_TYPE_ENCODING: usize = 3;

use backend::PrimeCharacteristicRing;
use utils::poseidon16_compress;

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

/// [tweak(2) | zeros(2) | public_param(4)]
///
/// Merkle LEFT input. Matches the LEFT-input convention for
/// `poseidon16_compress_half_hardcoded_left_4`: the first 4 FE come from the merkle
/// tweak slot at a compile-time absolute address, and the next 4 FE come from the
/// runtime `public_param` pointer — so the verifier never copies pp into a per-level
/// buffer.
pub(crate) fn build_left(tweak: [F; TWEAK_LEN], public_param: &PublicParam) -> [F; 8] {
    let mut left = [F::default(); 8];
    left[..TWEAK_LEN].copy_from_slice(&tweak);
    // left[TWEAK_LEN..INPUT_PREFIX_LEN] = zeros (default)
    left[INPUT_PREFIX_LEN..].copy_from_slice(public_param);
    left
}

/// [left_child(4) | right_child(4)]
///
/// Merkle RIGHT input: the two children of the parent node packed contiguously.
pub(crate) fn build_right(left_child: &Digest, right_child: &Digest) -> [F; 8] {
    let mut right = [F::default(); 8];
    right[..DIGEST_SIZE].copy_from_slice(left_child);
    right[DIGEST_SIZE..].copy_from_slice(right_child);
    right
}

/// Chain-hash-specific left layout: [tweak(2) | zeros(2) | data(4)].
pub(crate) fn build_left_chain(tweak: [F; TWEAK_LEN], data: &Digest) -> [F; 8] {
    let mut left = [F::default(); 8];
    left[..TWEAK_LEN].copy_from_slice(&tweak);
    // left[TWEAK_LEN..8-DIGEST_SIZE] = zeros (default)
    left[8 - DIGEST_SIZE..].copy_from_slice(data);
    left
}

/// Chain-hash-specific right layout: [public_param(4) | zeros(4)].
pub(crate) fn build_right_chain_pp(public_param: &PublicParam) -> [F; 8] {
    let mut right = [F::default(); 8];
    right[..PUBLIC_PARAM_LEN_FE].copy_from_slice(public_param);
    right
}

fn poseidon16_compress_with_trace(a: [F; 8], b: [F; 8], poseidon_16_trace: &mut Vec<([F; 16], [F; 8])>) -> [F; 8] {
    let input: [F; 16] = [a, b].concat().try_into().unwrap();
    let output = poseidon16_compress(input);
    poseidon_16_trace.push((input, output));
    output
}
