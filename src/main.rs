#![cfg_attr(not(test), allow(unused_crate_dependencies))]

mod examples;

use crate::examples::prove_poseidon2::{Poseidon2Config, prove_poseidon2};
use whir_p3::whir::config::{FoldingFactor, SecurityAssumption};

fn main() {
    let config = Poseidon2Config {
        log_n_poseidons_16: 17,
        log_n_poseidons_24: 17,
        univariate_skips: 4,
        folding_factor: FoldingFactor::new(7, 4),
        log_inv_rate: 1,
        soundness_type: SecurityAssumption::CapacityBound,
        pow_bits: 16,
        security_level: 128,
        rs_domain_initial_reduction_factor: 5,
        max_num_variables_to_send_coeffs: 3,
        display_logs: true,
    };
    let benchmark = prove_poseidon2(&config);
    println!("\n{benchmark}");
}
