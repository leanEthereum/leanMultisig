pub use multilinear_toolkit::prelude::{
    PrimeCharacteristicRing, // to allow `F::from_usize`
    ProofError,
};
pub use rec_aggregation::xmss_aggregate::{
    setup_xmss_aggregation, xmss_aggregate_signatures, xmss_verify_aggregated_signatures,
};
pub use whir_p3::precompute_dft_twiddles;
pub use xmss::{XMSS_MAX_LOG_LIFETIME, XmssPublicKey, XmssSecretKey, xmss_key_gen, xmss_sign, xmss_verify};

pub type F = p3_koala_bear::KoalaBear;

/*
WARNING: Toy XMSS, do not consider this secure (for now)!

For performance, don't forget:
1) RUSTFLAGS='-C target-cpu=native'
2) --release
*/

#[cfg(test)]
mod tests {
    use super::*;
    use xmss::{XMSS_MAX_LOG_LIFETIME, generate_phony_xmss_signatures};

    #[test]
    fn test_xmss_signature() {
        let first_slot = 555;
        let log_lifetime = 10;
        let slot = first_slot + 10;
        let key_gen_seed: [u8; 32] = std::array::from_fn(|i| i as u8);
        let randomness_seed: [u8; 32] = std::array::from_fn(|i| (i * 2) as u8);
        let message_hash: [F; 8] = std::array::from_fn(|i| F::from_usize(i * 3));

        let (secret_key, pub_key) = xmss_key_gen(key_gen_seed, first_slot, log_lifetime).unwrap();
        let signature = xmss_sign(randomness_seed, &secret_key, &message_hash, slot).unwrap();
        xmss_verify(&pub_key, &message_hash, &signature).unwrap();
    }

    #[test]
    fn test_aggregate_xmss_signature() {
        // Compile witness program to lean-ISA.
        // Should be called at the start of the program (both by prover or verifier).
        // (Otherwise the first call to `xmss_aggregate_signatures` or `xmss_verify_aggregated_signatures` will be slower)
        setup_xmss_aggregation();

        // Should only be called by the prover, at the start of the program
        //(Otherwise the first call to `xmss_aggregate_signatures` will be slower)
        precompute_dft_twiddles::<F>(1 << 24);

        let log_lifetimes = (1..=XMSS_MAX_LOG_LIFETIME).collect::<Vec<usize>>();
        let message_hash: [F; 8] = std::array::from_fn(|i| F::from_usize(i * 7));
        let first_slot = 77777;

        let (xmss_pub_keys, all_signatures) = generate_phony_xmss_signatures(&log_lifetimes, message_hash, first_slot);

        let proof = xmss_aggregate_signatures(&xmss_pub_keys, &all_signatures, message_hash).unwrap();
        xmss_verify_aggregated_signatures(&xmss_pub_keys, message_hash, &proof).unwrap();
    }
}
