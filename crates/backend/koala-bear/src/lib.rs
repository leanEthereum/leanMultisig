// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

//! The KoalaBear prime field and associated cryptographic primitives.

extern crate alloc;

mod koala_bear;
pub mod monty_31;
mod poseidon1_koalabear_16;
pub mod quintic_extension;
pub mod symmetric;

#[cfg(test)]
mod benchmark_poseidons;

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
mod aarch64_neon;

#[cfg(all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "avx512f")))]
mod x86_64_avx2;

#[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
mod x86_64_avx512;

pub use koala_bear::*;
pub use monty_31::*;
pub use poseidon1_koalabear_16::*;
pub use quintic_extension::*;

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
pub use aarch64_neon::*;

#[cfg(all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "avx512f")))]
pub use x86_64_avx2::*;

#[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
pub use x86_64_avx512::*;
