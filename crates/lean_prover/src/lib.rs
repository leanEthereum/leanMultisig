#![cfg_attr(not(test), allow(unused_crate_dependencies))]

use lean_vm::{EF, F};
use multilinear_toolkit::prelude::*;
use utils::*;

mod trace_gen;

pub mod prove_execution;
pub mod verify_execution;

#[cfg(test)]
mod test_zkvm;

use trace_gen::*;

// Right now, hash digests = 8 koala-bear (p = 2^31 - 2^24 + 1, i.e. ≈ 30.98 bits per field element)
// so ≈ 123.92 bits of security against collisions
pub const SECURITY_BITS: usize = 123; // TODO 128 bits security? (with Poseidon over 20 field elements or with a more subtle soundness analysis (cf. https://eprint.iacr.org/2021/188.pdf))

pub const GRINDING_BITS: usize = 18;

pub fn default_whir_config(starting_log_inv_rate: usize, prox_gaps_conjecture: bool) -> WhirConfigBuilder {
    WhirConfigBuilder {
        folding_factor: FoldingFactor::new(7, 5),
        soundness_type: if prox_gaps_conjecture {
            SecurityAssumption::CapacityBound // TODO update formula with State of Art Conjecture
        } else {
            SecurityAssumption::JohnsonBound
        },
        pow_bits: GRINDING_BITS,
        max_num_variables_to_send_coeffs: 9,
        rs_domain_initial_reduction_factor: 5,
        security_level: SECURITY_BITS,
        starting_log_inv_rate,
    }
}
