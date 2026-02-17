// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

#![cfg_attr(not(test), warn(unused_crate_dependencies))]

mod permutation;
pub use permutation::*;

mod sponge;
pub use sponge::*;

mod compression;
pub use compression::*;

pub mod merkle;
pub use merkle::DIGEST_ELEMS;
