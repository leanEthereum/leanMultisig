#![cfg_attr(not(test), allow(unused_crate_dependencies))]

use backend::*;
use lean_vm::{EF, F, MAX_WHIR_LOG_INV_RATE, MIN_WHIR_LOG_INV_RATE};
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
pub const MAX_NUM_VARIABLES_TO_SEND_COEFFS: usize = 8;
pub const WHIR_INITIAL_FOLDING_FACTOR: usize = 7;
pub const WHIR_SUBSEQUENT_FOLDING_FACTOR: usize = 5;
pub const RS_DOMAIN_INITIAL_REDUCTION_FACTOR: usize = 5;

pub const SNARK_DOMAIN_SEP: [F; 8] = F::new_array([
    130704175, 1303721200, 493664240, 1035493700, 2063844858, 1410214009, 1938905908, 1696767928,
]);

pub fn default_whir_config(starting_log_inv_rate: usize) -> WhirConfigBuilder {
    WhirConfigBuilder {
        folding_factor: FoldingFactor::new(WHIR_INITIAL_FOLDING_FACTOR, WHIR_SUBSEQUENT_FOLDING_FACTOR),
        soundness_type: if cfg!(feature = "prox-gaps-conjecture") {
            SecurityAssumption::CapacityBound // TODO update formula with State of the Art Conjecture
        } else {
            SecurityAssumption::JohnsonBound
        },
        pow_bits: GRINDING_BITS,
        max_num_variables_to_send_coeffs: MAX_NUM_VARIABLES_TO_SEND_COEFFS,
        rs_domain_initial_reduction_factor: RS_DOMAIN_INITIAL_REDUCTION_FACTOR,
        security_level: SECURITY_BITS,
        starting_log_inv_rate,
    }
}

pub(crate) fn check_rate(log_inv_rate: usize) -> Result<(), ProofError> {
    if (MIN_WHIR_LOG_INV_RATE..=MAX_WHIR_LOG_INV_RATE).contains(&log_inv_rate) {
        Ok(())
    } else {
        Err(ProofError::InvalidRate)
    }
}

#[cfg(test)]
mod tests {
    use backend::{PrimeCharacteristicRing, default_koalabear_poseidon1_16, hash_slice};
    use lean_vm::F;
    use rec_aggregation::{get_aggregation_bytecode, init_aggregation_bytecode};
    use utils::poseidon16_compress_pair;

    #[test]
    fn compute_snark_domain_sep() {
        init_aggregation_bytecode(2);
        let recursion_bytecode_hash = get_aggregation_bytecode(2).hash;
        let name_fe = "leanMultisig-0.6.0"
            .as_bytes()
            .iter()
            .map(|b| F::from_u8(*b))
            .collect::<Vec<_>>();
        let mut prefix_free_name_fe = vec![F::ZERO; 8];
        let len = name_fe.len();
        prefix_free_name_fe.extend(name_fe);
        while prefix_free_name_fe.len() % 8 != 7 {
            prefix_free_name_fe.push(F::ZERO);
        }
        prefix_free_name_fe.push(F::from_u64(len as u64));
        let comp = default_koalabear_poseidon1_16();
        let name_hash = hash_slice::<_, _, _, 8, 8>(&comp, &prefix_free_name_fe);

        // We incorporate the recursion program hash, containing all the verifier logic, into fiat shamir domain separator
        // (likely not necessary but why not, is there a cleaner approach?)
        let domain_sep = poseidon16_compress_pair(&name_hash, &recursion_bytecode_hash);

        println!("Computed SNARK_DOMAIN_SEP: {:?}", domain_sep); // We dont assert equality here to avoid the pain of having to update the hardcoded SNARK_DOMAIN_SEP every time we change the recursion program
    }
}
