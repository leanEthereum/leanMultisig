#![cfg_attr(not(test), warn(unused_crate_dependencies))]
pub mod signers_cache;
mod wots;
use backend::*;
use utils::{poseidon16_compress, poseidon24_compress};
pub use wots::*;
mod xmss;
pub use xmss::*;

pub(crate) const DIGEST_SIZE: usize = 8;

type F = KoalaBear;
type Digest = [F; DIGEST_SIZE];

// WOTS
pub const V: usize = 46;
pub const W: usize = 3;
pub const CHAIN_LENGTH: usize = 1 << W;
pub const TARGET_SUM: usize = 200;
pub const LOG_LIFETIME: usize = 32;
pub const RANDOMNESS_LEN_FE: usize = 7;
pub const MESSAGE_LEN_FE: usize = 9;
pub const PUBLIC_PARAM_LEN_FE: usize = 5;
pub const TWEAK_LEN: usize = 2;
pub const POSEIDON24_CAPACITY: usize = 9;
pub const POSEIDON24_RATE: usize = 15;

pub type PublicParam = [F; PUBLIC_PARAM_LEN_FE];

pub const SIG_SIZE_FE: usize = RANDOMNESS_LEN_FE + (V + LOG_LIFETIME) * DIGEST_SIZE;

pub type Poseidon24History = Vec<([F; 24], [F; 9])>;
pub type Poseidon16History = Vec<([F; 16], [F; 8])>;

// Tweak types for domain separation
pub const TWEAK_TYPE_CHAIN: usize = 0;
pub const TWEAK_TYPE_WOTS_PK: usize = 1;
pub const TWEAK_TYPE_MERKLE: usize = 2;
pub const TWEAK_TYPE_ENCODING: usize = 3;

/// Construct a domain-separation tweak from a type, sub-position, and index (e.g. slot or node index).
/// First element packs: tweak_type (bits 26-27), index_hi (bits 10-25), sub_position (bits 0-9).
/// Second element: index_lo (bits 0-15).
pub fn make_tweak(tweak_type: usize, sub_position: usize, index: u32) -> [F; TWEAK_LEN] {
    debug_assert!(sub_position < 1024, "sub_position must fit in 10 bits");
    debug_assert!(tweak_type < 4, "tweak_type must fit in 2 bits");
    let index_lo = (index & 0xFFFF) as usize;
    let index_hi = ((index >> 16) & 0xFFFF) as usize;
    [
        F::from_usize((tweak_type << 26) | (index_hi << 10) | sub_position),
        F::from_usize(index_lo),
    ]
}

fn poseidon16_compress_with_trace(input: [F; 16], trace: &mut Poseidon16History) -> Digest {
    let output = poseidon16_compress(input);
    trace.push((input, output));
    output
}

fn poseidon24_compress_with_trace(input: [F; 24], trace: &mut Poseidon24History) -> [F; 9] {
    let output = poseidon24_compress(input);
    trace.push((input, output));
    output
}

/// Poseidon24 merkle tree hash: compress(left(8) || right(8) || tweak(2) || public_param(5) || 0)
pub fn merkle_hash(left: &Digest, right: &Digest, level: usize, node_index: u32, public_param: &PublicParam) -> Digest {
    let tweak = make_tweak(TWEAK_TYPE_MERKLE, level, node_index);
    let mut input = [F::ZERO; 24];
    input[0..8].copy_from_slice(left);
    input[8..16].copy_from_slice(right);
    input[16..18].copy_from_slice(&tweak);
    input[18..23].copy_from_slice(public_param);
    poseidon24_compress(input)[..DIGEST_SIZE].try_into().unwrap()
}

fn merkle_hash_with_trace(
    left: &Digest,
    right: &Digest,
    level: usize,
    node_index: u32,
    public_param: &PublicParam,
    trace: &mut Poseidon24History,
) -> Digest {
    let tweak = make_tweak(TWEAK_TYPE_MERKLE, level, node_index);
    let mut input = [F::ZERO; 24];
    input[0..8].copy_from_slice(left);
    input[8..16].copy_from_slice(right);
    input[16..18].copy_from_slice(&tweak);
    input[18..23].copy_from_slice(public_param);
    poseidon24_compress_with_trace(input, trace)[..DIGEST_SIZE]
        .try_into()
        .unwrap()
}
