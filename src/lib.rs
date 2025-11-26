pub use xmss::{XmssPublicKey, XmssSecretKey, xmss_key_gen, xmss_sign, xmss_verify};

pub use multilinear_toolkit::prelude::PrimeCharacteristicRing; // to allow `F::from_usize`

pub type F = p3_koala_bear::KoalaBear;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_xmss_signature_end_2_end() {
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
}
