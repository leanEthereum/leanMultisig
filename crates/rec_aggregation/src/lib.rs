#![cfg_attr(not(test), allow(unused_crate_dependencies))]

use leansig::signature::generalized_xmss::instantiations_poseidon_top_level::lifetime_2_to_the_32::hashing_optimized as leansig_module;

pub mod xmss_aggregate;

pub type LeanSigScheme = leansig_module::SIGTopLevelTargetSumLifetime32Dim64Base8;
pub type LeanSigPubKey = leansig_module::PubKeyTopLevelTargetSumLifetime32Dim64Base8;
pub type LeanSigSignature = leansig_module::SigTopLevelTargetSumLifetime32Dim64Base8;

#[cfg(test)]
mod tests {
    use super::*;
    use leansig::signature::{SignatureScheme, SignatureSchemeSecretKey};
    use rand::{Rng, SeedableRng, rngs::StdRng};

    #[test]
    fn test() {
        let mut rng = StdRng::seed_from_u64(0);
        let activation_epoch = 123456;
        let lifetime = 1 << 13;
        let (pk, mut sk) = LeanSigScheme::key_gen(&mut rng, activation_epoch, lifetime);
        let message = rng.random();
        let epoch = rng.random_range(activation_epoch..activation_epoch + lifetime) as u32;
        let mut iterations = 0;
        while !sk.get_prepared_interval().contains(&(epoch as u64)) && iterations < epoch {
            sk.advance_preparation();
            iterations += 1;
        }
        let sig = LeanSigScheme::sign(&sk, epoch, &message).unwrap();
        let is_valid = LeanSigScheme::verify(&pk, epoch, &message, &sig);
        assert!(is_valid);
    }
}
