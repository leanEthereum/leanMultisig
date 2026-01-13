pub use multilinear_toolkit::prelude::ProofError;

pub use rec_aggregation::xmss_aggregate::{
    Devnet2XmssAggregateSignature, XmssAggregateError, xmss_aggregate_signatures, xmss_verify_aggregated_signatures,
};

pub fn xmss_aggregation_setup_prover() {
    rec_aggregation::xmss_aggregate::xmss_setup_aggregation_program();
    whir_p3::precompute_dft_twiddles::<p3_koala_bear::KoalaBear>(1 << 24);
}

pub fn xmss_aggregation_setup_verifier() {
    rec_aggregation::xmss_aggregate::xmss_setup_aggregation_program();
}

#[cfg(test)]
mod tests {
    use rand::{SeedableRng, rngs::StdRng};
    use rec_aggregation::xmss_aggregate::gen_pubkey_and_signature;

    use super::*;

    // Should be run in release mode
    #[test]
    fn test_aggregate_xmss_signature() {
        // Not mandatory, but avoid to slow down the first aggregation proof
        xmss_aggregation_setup_prover();

        // Not mandatory, but avoid to slow down the first aggregation verification
        // (Actually, no need to call it if `xmss_aggregation_setup_prover` was already called)
        xmss_aggregation_setup_verifier();

        let key_log_lifetimes = vec![5, 6, 7];
        let key_activation_epoch = vec![10, 20, 30];

        let epoch = 50;
        let message_hash: [u8; 32] = [42u8; 32];

        let mut rng = StdRng::seed_from_u64(0);
        let (xmss_pub_keys, all_signatures) = key_log_lifetimes
            .iter()
            .zip(key_activation_epoch.iter())
            .map(|(log_lifetime, activation_epoch)| {
                gen_pubkey_and_signature(*log_lifetime, *activation_epoch, epoch, &message_hash, &mut rng)
            })
            .unzip::<_, _, Vec<_>, Vec<_>>();

        let agg_sig = xmss_aggregate_signatures(&xmss_pub_keys, &all_signatures, &message_hash, epoch).unwrap();
        xmss_verify_aggregated_signatures(&xmss_pub_keys, &message_hash, &agg_sig, epoch).unwrap();

        assert!(xmss_verify_aggregated_signatures(&xmss_pub_keys, &message_hash, &agg_sig, epoch).is_ok());

        let invalid_message_hash: [u8; 32] = [43u8; 32];
        assert!(xmss_verify_aggregated_signatures(&xmss_pub_keys, &invalid_message_hash, &agg_sig, epoch).is_err());

        let invalid_epoch = epoch + 1;
        assert!(xmss_verify_aggregated_signatures(&xmss_pub_keys, &message_hash, &agg_sig, invalid_epoch).is_err());

        let mut invalid_pub_keys = xmss_pub_keys.clone();
        invalid_pub_keys[0] = invalid_pub_keys[1].clone();
        assert!(xmss_verify_aggregated_signatures(&invalid_pub_keys, &message_hash, &agg_sig, epoch).is_err());
    }
}
