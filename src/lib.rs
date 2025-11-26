pub use multilinear_toolkit::prelude::{
    PrimeCharacteristicRing, // to allow `F::from_usize`
    ProofError,
};
pub use rec_aggregation::xmss_aggregate::{xmss_aggregate_signatures, xmss_verify_aggregated_signatures};
pub use xmss::{
    XMSS_MAX_LOG_LIFETIME,
    XmssPublicKey,
    XmssSecretKey,
    xmss_generate_phony_signatures, // useful for tests
    xmss_key_gen,
    xmss_sign,
    xmss_verify,
};

pub fn xmss_aggregation_setup_prover() {
    rec_aggregation::xmss_aggregate::xmss_setup_aggregation_program();
    whir_p3::precompute_dft_twiddles::<F>(1 << 24);
}

pub fn xmss_aggregation_setup_verifier() {
    rec_aggregation::xmss_aggregate::xmss_setup_aggregation_program();
}

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
        xmss_verify(&pub_key, &message_hash, &signature, slot).unwrap();
    }

    #[test]
    fn test_aggregate_xmss_signature() {
        // Not mandatory, but avoid to slow down the first aggregation proof
        xmss_aggregation_setup_prover();

        // Not mandatory, but avoid to slow down the first aggregation verification
        // (Actually, no need to call it if `xmss_aggregation_setup_prover` was already called)
        xmss_aggregation_setup_verifier();

        let log_lifetimes = (10..=XMSS_MAX_LOG_LIFETIME).collect::<Vec<usize>>();
        let message_hash: [F; 8] = std::array::from_fn(|i| F::from_usize(i * 7));
        let slot = 1 << 33;

        let (xmss_pub_keys, all_signatures) = xmss_generate_phony_signatures(&log_lifetimes, message_hash, slot);

        let proof = xmss_aggregate_signatures(&xmss_pub_keys, &all_signatures, message_hash, slot).unwrap();
        xmss_verify_aggregated_signatures(&xmss_pub_keys, message_hash, &proof, slot).unwrap();
    }
}
