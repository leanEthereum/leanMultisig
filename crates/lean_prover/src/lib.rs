#![cfg_attr(not(test), allow(unused_crate_dependencies))]

use lean_vm::{EF, F};
use utils::*;

use lean_vm::execute_bytecode;
use whir_p3::{FoldingFactor, SecurityAssumption, WhirConfigBuilder};
use witness_generation::*;

mod common;
pub mod prove_execution;
pub mod verify_execution;

const UNIVARIATE_SKIPS: usize = 3;
const LOG_SMALLEST_DECOMPOSITION_CHUNK: usize = 8; // TODO optimize

pub fn whir_config_builder() -> WhirConfigBuilder {
    WhirConfigBuilder {
        folding_factor: FoldingFactor::new(7, 4),
        soundness_type: SecurityAssumption::CapacityBound,
        pow_bits: 16,
        max_num_variables_to_send_coeffs: 6,
        rs_domain_initial_reduction_factor: 5,
        security_level: 128,
        starting_log_inv_rate: 1,
    }
}

const TABLE_INDEX_POSEIDONS_16: usize = 1; // should be != 0
const TABLE_INDEX_POSEIDONS_24: usize = 2;
const TABLE_INDEX_DOT_PRODUCTS: usize = 3;
const TABLE_INDEX_MULTILINEAR_EVAL: usize = 4;
