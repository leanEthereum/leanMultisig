// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

//! AVX2 helpers shared by Poseidon1 permutations.
//!
//! The optimised batched-S-box helpers (`exp_small`, `add_rc_and_sbox`,
//! `sbox`, `InternalLayer16`) relied on a "signed in (-P, P)" intermediate
//! stored as i32, which is unambiguous only for `P < 2^31`. They have
//! been removed for the current 32-bit prime; AVX2 Poseidon falls through
//! the generic `permute_generic` path which uses canonical Mul.
