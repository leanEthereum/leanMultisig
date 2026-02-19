// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

//! The KoalaBear prime field and associated cryptographic primitives.

extern crate alloc;

mod koala_bear;
pub mod monty_31;
pub mod poseidon2;
mod poseidon2_koalabear;
pub mod quintic_extension;
pub mod symmetric;

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
mod aarch64_neon;

#[cfg(all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "avx512f")))]
mod x86_64_avx2;

#[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
mod x86_64_avx512;

// Re-export everything from monty_31
pub use monty_31::*;

// Re-export koala bear specific types
pub use koala_bear::*;

// Re-export koala bear poseidon2 constants and types
pub use poseidon2_koalabear::*;

// Re-export key poseidon2 types
pub use poseidon2::{
    ExternalLayer, ExternalLayerConstants, ExternalLayerConstructor, GenericPoseidon2LinearLayers, HLMDSMat4,
    InternalLayer, InternalLayerConstructor, MDSMat4, Poseidon2, add_rc_and_sbox_generic,
    external_initial_permute_state, external_terminal_permute_state, mds_light_permutation,
    poseidon2_round_numbers_128,
};

// Re-export quintic extension types
pub use quintic_extension::*;

// Re-export arch-specific types
#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
pub use aarch64_neon::*;

#[cfg(all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "avx512f")))]
pub use x86_64_avx2::*;

#[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
pub use x86_64_avx512::*;
