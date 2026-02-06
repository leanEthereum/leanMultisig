use multilinear_toolkit::prelude::*;
pub use multilinear_toolkit::prelude::{
    PrimeCharacteristicRing, // to allow `F::from_usize`
    ProofError,
};
pub use rec_aggregation::xmss_aggregate::{xmss_aggregate_signatures, xmss_verify_aggregated_signatures};
pub use xmss::{XmssPublicKey, XmssSecretKey, XmssSignature, xmss_key_gen, xmss_sign, xmss_verify};

pub fn xmss_aggregation_setup_prover() {
    rec_aggregation::xmss_aggregate::xmss_setup_aggregation_program();
    precompute_dft_twiddles::<F>(1 << 24);
}

pub fn xmss_aggregation_setup_verifier() {
    rec_aggregation::xmss_aggregate::xmss_setup_aggregation_program();
}

pub type F = p3_koala_bear::KoalaBear;

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{Rng, SeedableRng, rngs::StdRng};
    use xmss::MESSAGE_LEN_FE;

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
    fn test_aggregate_xmss_signature() {
        // Not mandatory, but avoid to slow down the first aggregation proof
        xmss_aggregation_setup_prover();

        // Not mandatory, but avoid to slow down the first aggregation verification
        // (Actually, no need to call it if `xmss_aggregation_setup_prover` was already called)
        xmss_aggregation_setup_verifier();

        let n_signatures = 3;
        let message_hash: [F; MESSAGE_LEN_FE] = std::array::from_fn(|i| F::from_usize(i * 7));
        let slot = 77777;

        let pub_keys_and_sigs: Vec<_> = (0..n_signatures)
            .into_par_iter()
            .map(|i| {
                let mut rng = StdRng::seed_from_u64(i as u64);
                let start = slot - 5;
                let end = slot + 5;
                let (sk, pk) = xmss_key_gen(rng.random(), start, end).unwrap();
                let sig = xmss_sign(&mut rng, &sk, &message_hash, slot).unwrap();
                xmss_verify(&pk, &message_hash, &sig).unwrap();
                (pk, sig)
            })
            .collect();
        let (xmss_pub_keys, all_signatures): (Vec<_>, Vec<_>) = pub_keys_and_sigs.into_iter().unzip();

        let log_inv_rate = 1;
        let prox_gaps_conjecture = false;
        let proof = xmss_aggregate_signatures(
            &xmss_pub_keys,
            &all_signatures,
            message_hash,
            slot,
            log_inv_rate,
            prox_gaps_conjecture,
        )
        .unwrap();
        xmss_verify_aggregated_signatures(
            &xmss_pub_keys,
            message_hash,
            &proof,
            slot,
            log_inv_rate,
            prox_gaps_conjecture,
        )
        .unwrap();
    }
}
