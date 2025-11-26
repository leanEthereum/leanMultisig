#![cfg_attr(not(test), warn(unused_crate_dependencies))]
use p3_koala_bear::KoalaBear;

mod wots;
use utils::{poseidon16_permute, poseidon24_permute};
pub use wots::*;
mod xmss;
pub use xmss::*;
mod phony_xmss;
pub use phony_xmss::*;

type F = KoalaBear;
type Digest = [F; 8];

// WOTS
pub const V: usize = 66;
pub const W: usize = 4;
pub const CHAIN_LENGTH: usize = 1 << W;
pub const D: usize = 80;
pub const TARGET_SUM: usize = V * (W - 1) - D;
pub const XMSS_MAX_LOG_LIFETIME: usize = 30;

pub type Poseidon16History = Vec<([F; 16], [F; 16])>;
pub type Poseidon24History = Vec<([F; 24], [F; 8])>;

fn poseidon16_compress(a: &Digest, b: &Digest) -> Digest {
    poseidon16_permute([*a, *b].concat().try_into().unwrap())[0..8]
        .try_into()
        .unwrap()
}

fn poseidon16_compress_with_trace(a: &Digest, b: &Digest, poseidon_16_trace: &mut Vec<([F; 16], [F; 16])>) -> Digest {
    let input: [F; 16] = [*a, *b].concat().try_into().unwrap();
    let output = poseidon16_permute(input);
    poseidon_16_trace.push((input, output));
    output[0..8].try_into().unwrap()
}

fn poseidon24_compress(a: &Digest, b: &Digest, c: &Digest) -> Digest {
    poseidon24_permute([*a, *b, *c].concat().try_into().unwrap())[16..24]
        .try_into()
        .unwrap()
}

fn poseidon24_compress_with_trace(
    a: &Digest,
    b: &Digest,
    c: &Digest,
    poseidon_24_trace: &mut Vec<([F; 24], [F; 8])>,
) -> Digest {
    let input: [F; 24] = [*a, *b, *c].concat().try_into().unwrap();
    let output = poseidon24_permute(input)[16..24].try_into().unwrap();
    poseidon_24_trace.push((input, output));
    output
}
