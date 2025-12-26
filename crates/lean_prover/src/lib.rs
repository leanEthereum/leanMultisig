#![cfg_attr(not(test), allow(unused_crate_dependencies))]

use lean_vm::{EF, F};
use utils::*;

use lean_vm::execute_bytecode;
use whir_p3::{FoldingFactor, SecurityAssumption, WhirConfigBuilder};
use witness_generation::*;

mod common;
pub mod prove_execution;
#[cfg(test)]
mod test_zkvm;
pub mod verify_execution;

pub const UNIVARIATE_SKIPS: usize = 3;

#[derive(Debug)]
pub struct SnarkParams {
    pub first_whir: WhirConfigBuilder,
    pub second_whir: WhirConfigBuilder,
}

impl Default for SnarkParams {
    fn default() -> Self {
        Self {
            first_whir: whir_config_builder(1, 7, 5),
            second_whir: whir_config_builder(3, 4, 1),
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
        soundness_type: SecurityAssumption::CapacityBound,
        pow_bits: 16,
        max_num_variables_to_send_coeffs: 6,
        rs_domain_initial_reduction_factor,
        security_level: 128,
        starting_log_inv_rate,
    }
}
