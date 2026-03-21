use std::array;

use backend::{KoalaBear, integers::QuotientMap};
use leansig::{
    signature::generalized_xmss::{
        instantiations_aborting::lifetime_2_to_the_32::SigAbortingTargetSumLifetime32Dim64Base8,
        instantiations_poseidon_top_level::lifetime_2_to_the_32::hashing_optimized::{
            PubKeyTopLevelTargetSumLifetime32Dim64Base8, SIGTopLevelTargetSumLifetime32Dim64Base8,
        },
    },
    symmetric::tweak_hash::poseidon::PoseidonTweakHash,
};
use p3_field::PrimeField32;

pub const V: usize = 46;
pub const W: usize = 3;
pub const CHAIN_LENGTH: usize = 1 << W;
pub const TARGET_SUM: usize = 200;
pub const LOG_LIFETIME: usize = 32;
pub const RANDOMNESS_LEN_FE: usize = 7;
pub const MESSAGE_LEN_FE: usize = 9;
pub const PUBLIC_PARAM_LEN_FE: usize = 5;
pub const TWEAK_LEN: usize = 2;
pub const POSEIDON24_CAPACITY: usize = 9;
pub const POSEIDON24_RATE: usize = 15;
pub const DIGEST_SIZE_FE: usize = 8;

pub const SIG_SIZE_FE: usize = RANDOMNESS_LEN_FE + (V + LOG_LIFETIME) * DIGEST_SIZE_FE;

pub(crate) type F = KoalaBear;

pub const WOTS_PUBKET_SPONGE_DOMAIN_SEP: [F; POSEIDON24_CAPACITY] = F::new_array([
    2060061975, 916902315, 229801915, 83751504, 2093549181, 1743125625, 721042244, 1252069948, 1192880636,
]);

pub use leansig::symmetric::tweak_hash::TweakableHash;

pub type LeanSigTH = PoseidonTweakHash<PUBLIC_PARAM_LEN_FE, DIGEST_SIZE_FE, TWEAK_LEN, POSEIDON24_CAPACITY, V>;

pub type LeanSigScheme = SIGTopLevelTargetSumLifetime32Dim64Base8;
pub type XmssPublicKey = PubKeyTopLevelTargetSumLifetime32Dim64Base8;
pub type LeanSigSignature = SigAbortingTargetSumLifetime32Dim64Base8;

pub fn pubkey_merkle_root(pub_keys: &XmssPublicKey) -> [F; DIGEST_SIZE_FE] {
    assert_eq!(pub_keys.root().len(), DIGEST_SIZE_FE);
    array::from_fn(|i| F::from_canonical_checked(pub_keys.root()[i].as_canonical_u32()).unwrap())
}

pub fn pubkey_public_parameter(pub_keys: &XmssPublicKey) -> [F; PUBLIC_PARAM_LEN_FE] {
    assert_eq!(pub_keys.parameter().len(), PUBLIC_PARAM_LEN_FE);
    array::from_fn(|i| F::from_canonical_checked(pub_keys.parameter()[i].as_canonical_u32()).unwrap())
}

pub fn chain_tweak(slot: u32, chain_idx: u32, step: u32) -> [F; TWEAK_LEN] {
    let [t0, t1] = LeanSigTH::chain_tweak(slot, chain_idx as u8, step as u8).to_field_elements();
    [
        F::from_canonical_checked(t0.as_canonical_u32()).unwrap(),
        F::from_canonical_checked(t1.as_canonical_u32()).unwrap(),
    ]
}

pub fn merkle_tweak(level: usize, pos_in_level: u32) -> [F; TWEAK_LEN] {
    let [t0, t1] = LeanSigTH::tree_tweak(level as u8, pos_in_level).to_field_elements();
    [
        F::from_canonical_checked(t0.as_canonical_u32()).unwrap(),
        F::from_canonical_checked(t1.as_canonical_u32()).unwrap(),
    ]
}

pub fn xmss_merkle_path(sig: &LeanSigSignature) -> &Vec<[F; DIGEST_SIZE_FE]> {
    unsafe { std::mem::transmute(sig.path()) }
}

pub fn xmss_randomness(sig: &LeanSigSignature) -> &[F; RANDOMNESS_LEN_FE] {
    unsafe { std::mem::transmute(sig.rho()) }
}

pub fn xmmss_revealed_chain_tips(sig: &LeanSigSignature) -> &Vec<[F; DIGEST_SIZE_FE]> {
    unsafe { std::mem::transmute(sig.hashes()) }
}