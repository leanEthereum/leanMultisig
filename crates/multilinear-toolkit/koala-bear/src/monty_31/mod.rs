// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

//! An abstraction of 31-bit fields which use a MONTY approach for faster multiplication.

mod data_traits;
mod monty_31;
pub(crate) mod poseidon2_monty;
pub(crate) mod utils;

// Skip mds.rs for now - requires karatsuba_convolution dependency
// mod mds;

#[cfg(not(any(
    all(target_arch = "aarch64", target_feature = "neon"),
    all(target_arch = "x86_64", target_feature = "avx2",),
)))]
pub(crate) mod no_packing;
#[cfg(not(any(
    all(target_arch = "aarch64", target_feature = "neon"),
    all(target_arch = "x86_64", target_feature = "avx2",),
)))]
pub use no_packing::*;

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
pub(crate) mod aarch64_neon;
#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
pub use aarch64_neon::*;

#[cfg(all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "avx512f")))]
pub(crate) mod x86_64_avx2;
#[cfg(all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "avx512f")))]
pub use x86_64_avx2::*;

#[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
pub(crate) mod x86_64_avx512;
#[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
pub use x86_64_avx512::*;

pub use data_traits::*;
pub use monty_31::*;
pub use poseidon2_monty::*;
pub use utils::{monty_add, monty_sub};
