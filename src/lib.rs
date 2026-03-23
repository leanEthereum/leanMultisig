use backend::*;

pub use backend::ProofError;
pub use rec_aggregation::{AggregatedXMSS, AggregationTopology, xmss_aggregate, xmss_verify_aggregation};

pub type F = KoalaBear;

/// Call once before proving. Compiles the aggregation program and precomputes DFT twiddles.
pub fn setup_prover() {
    rec_aggregation::init_aggregation_bytecode();
    precompute_dft_twiddles::<F>(1 << 24);
}

/// Call once before verifying (not needed if `setup_prover` was already called).
pub fn setup_verifier() {
    rec_aggregation::init_aggregation_bytecode();
}

#[cfg(test)]
mod tests {
    use super::*;
    use leansig_wrapper::{MESSAGE_LENGTH, xmss_keygen_fast, xmss_sign_fast, xmss_verify};
    use rand::{SeedableRng, rngs::StdRng};
    use rec_aggregation::signatures_cache::{BENCHMARK_MESSAGE, BENCHMARK_SLOT, get_benchmark_signatures};

    #[test]
    fn test_xmss_signature() {
        let start = 555;
        let end = 565;
        let slot = 560;
        let mut rng = StdRng::seed_from_u64(0);
        let message_hash: [u8; MESSAGE_LENGTH] = std::array::from_fn(|i| i as u8);

        let (secret_key, pub_key) = xmss_keygen_fast(&mut rng, start, end);
        let signature = xmss_sign_fast(&secret_key, &message_hash, slot).unwrap();
        xmss_verify(&pub_key, slot, &message_hash, &signature).unwrap();
    }

    #[test]
    fn test_recursive_aggregation() {
        setup_prover();

        let log_inv_rate = 2; // [1, 2, 3 or 4] (lower = faster but bigger proofs)
        let message = BENCHMARK_MESSAGE;
        let slot: u32 = BENCHMARK_SLOT;
        let signatures = get_benchmark_signatures();

        let pub_keys_and_sigs_a = signatures[0..3].to_vec();
        let aggregated_a = xmss_aggregate(&[], pub_keys_and_sigs_a, &message, slot, log_inv_rate);

        let pub_keys_and_sigs_b = signatures[3..5].to_vec();
        let aggregated_b = xmss_aggregate(&[], pub_keys_and_sigs_b, &message, slot, log_inv_rate);

        let pub_keys_and_sigs_c = signatures[5..6].to_vec();

        let aggregated_final = xmss_aggregate(
            &[aggregated_a, aggregated_b],
            pub_keys_and_sigs_c,
            &message,
            slot,
            log_inv_rate,
        );

        let serialized_final = aggregated_final.serialize();
        println!("Serialized aggregated final: {} KiB", serialized_final.len() / 1024);
        let deserialized_final = AggregatedXMSS::deserialize(&serialized_final).unwrap();

        xmss_verify_aggregation(&deserialized_final, &message, slot).unwrap();
    }
}
