use multilinear_toolkit::prelude::*;

pub use multilinear_toolkit::prelude::ProofError;
pub use rec_aggregation::{AggregatedSigs, AggregationTopology, Digest, aggregate, verify_aggregation};
pub use xmss::{MESSAGE_LEN_FE, XmssPublicKey, XmssSecretKey, XmssSignature, xmss_key_gen, xmss_sign, xmss_verify};

pub type F = p3_koala_bear::KoalaBear;

/// Call once before proving. Compiles the aggregation program and precomputes DFT twiddles.
pub fn setup_prover() {
    rec_aggregation::compilation::init_aggregation_bytecode();
    precompute_dft_twiddles::<F>(1 << 24);
}

/// Call once before verifying (not needed if `setup_prover` was already called).
pub fn setup_verifier() {
    rec_aggregation::compilation::init_aggregation_bytecode();
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{SeedableRng, rngs::StdRng};
    use xmss::signers_cache::{
        BENCHMARK_SLOT, find_randomness_for_benchmark, message_for_benchmark, reconstruct_signer_for_benchmark,
    };

    #[test]
    fn test_xmss_signature() {
        let start = 555;
        let end = 565;
        let slot = 560;
        let key_gen_seed: [u8; 32] = std::array::from_fn(|i| i as u8);
        let message_hash: [F; MESSAGE_LEN_FE] = std::array::from_fn(|i| F::from_usize(i * 3));

        let (secret_key, pub_key) = xmss_key_gen(key_gen_seed, start, end).unwrap();
        let mut rng = StdRng::from_seed(std::array::from_fn(|i| (i * 2) as u8));
        let signature = xmss_sign(&mut rng, &secret_key, &message_hash, slot).unwrap();
        xmss_verify(&pub_key, &message_hash, &signature).unwrap();
    }

    #[test]
    fn test_recursive_aggregation() {
        setup_prover();

        let log_inv_rate = 1;
        let prox_gaps_conjecture = false;
        let message: [F; MESSAGE_LEN_FE] = message_for_benchmark();
        let slot: u32 = BENCHMARK_SLOT;

        let pub_keys_and_sigs_a: Vec<_> = (0..3)
            .into_par_iter()
            .map(|i| reconstruct_signer_for_benchmark(i, find_randomness_for_benchmark(i)))
            .collect();
        let aggregated_a = aggregate(
            &[],
            pub_keys_and_sigs_a,
            &message,
            slot,
            log_inv_rate,
            prox_gaps_conjecture,
            false,
        );

        let pub_keys_and_sigs_b: Vec<_> = (3..5)
            .into_par_iter()
            .map(|i| reconstruct_signer_for_benchmark(i, find_randomness_for_benchmark(i)))
            .collect();
        let aggregated_b = aggregate(
            &[],
            pub_keys_and_sigs_b,
            &message,
            slot,
            log_inv_rate,
            prox_gaps_conjecture,
            false,
        );

        let pub_keys_and_sigs_c: Vec<_> = (5..6)
            .into_par_iter()
            .map(|i| reconstruct_signer_for_benchmark(i, find_randomness_for_benchmark(i)))
            .collect();

        let aggregated_final = aggregate(
            &[aggregated_a, aggregated_b],
            pub_keys_and_sigs_c,
            &message,
            slot,
            log_inv_rate,
            prox_gaps_conjecture,
            false,
        );

        verify_aggregation(&aggregated_final, &message, slot, prox_gaps_conjecture).unwrap();
    }
}
