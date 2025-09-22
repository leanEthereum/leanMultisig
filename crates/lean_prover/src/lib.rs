#![cfg_attr(not(test), allow(unused_crate_dependencies))]

use lean_vm::{EF, F};
use utils::*;
use whir_p3::whir::config::{FoldingFactor, SecurityAssumption, WhirConfigBuilder};

use lean_vm::execute_bytecode;
use witness_generation::*;

mod common;
pub mod prove_execution;
pub mod verify_execution;

const UNIVARIATE_SKIPS: usize = 3;
const LOG_SMALLEST_DECOMPOSITION_CHUNK: usize = 8; // TODO optimize

pub fn whir_config_builder() -> MyWhirConfigBuilder {
    WhirConfigBuilder {
        folding_factor: FoldingFactor::new(7, 4),
        soundness_type: SecurityAssumption::CapacityBound,
        merkle_hash: build_merkle_hash(),
        merkle_compress: build_merkle_compress(),
        pow_bits: 16,
        max_num_variables_to_send_coeffs: 6,
        rs_domain_initial_reduction_factor: 5,
        security_level: 128,
        starting_log_inv_rate: 1,
    }
}
