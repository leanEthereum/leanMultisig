#![cfg_attr(not(test), allow(unused_crate_dependencies))]

use lean_vm::{EF, F};
use multilinear_toolkit::prelude::*;
use utils::*;

use lean_vm::execute_bytecode;
use witness_generation::*;

mod common;
pub mod prove_execution;
#[cfg(test)]
mod test_zkvm;
pub mod verify_execution;

pub use witness_generation::bytecode_to_multilinear_polynomial;

// Right now, hash digests = 8 koala-bear (p = 2^31 - 2^24 + 1, i.e. ≈ 30.98 bits per field element)
// so ≈ 123.92 bits of security against collisions
pub const SECURITY_BITS: usize = 123; // TODO 128 bits security (with Poseidon over 20 field elements)

// Provable security (no proximity gaps conjectures)
pub const SECURITY_REGIME: SecurityAssumption = SecurityAssumption::JohnsonBound;

pub const GRINDING_BITS: usize = 16;

pub const STARTING_LOG_INV_RATE_BASE: usize = 2;

pub const STARTING_LOG_INV_RATE_EXTENSION: usize = 3;

#[derive(Debug)]
pub struct SnarkParams {
    pub first_whir: WhirConfigBuilder,
    pub second_whir: WhirConfigBuilder,
}

impl Default for SnarkParams {
    fn default() -> Self {
        Self {
            first_whir: whir_config_builder(STARTING_LOG_INV_RATE_BASE, 7, 5),
            second_whir: whir_config_builder(STARTING_LOG_INV_RATE_EXTENSION, 4, 1),
        }
    }
}

pub fn whir_config_builder(
    starting_log_inv_rate: usize,
    first_folding_factor: usize,
    rs_domain_initial_reduction_factor: usize,
) -> WhirConfigBuilder {
    WhirConfigBuilder {
        folding_factor: FoldingFactor::new(first_folding_factor, 4),
        soundness_type: SECURITY_REGIME,
        pow_bits: GRINDING_BITS,
        max_num_variables_to_send_coeffs: 6,
        rs_domain_initial_reduction_factor,
        security_level: SECURITY_BITS,
        starting_log_inv_rate,
    }
}
