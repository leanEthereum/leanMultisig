// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

//! The Goldilocks prime field `F_p` where `p = 2^64 - 2^32 + 1`, and a degree-3 extension.
//!
//! This is a port of `plonky3/goldilocks/` adapted to the in-tree `field` trait crate.

extern crate alloc;

mod cubic_extension;
mod goldilocks;
mod helpers;
mod poseidon1;

#[cfg(test)]
mod benchmark_poseidons_goldilocks;

pub use cubic_extension::*;
pub use goldilocks::*;
pub use helpers::*;
pub use poseidon1::*;
