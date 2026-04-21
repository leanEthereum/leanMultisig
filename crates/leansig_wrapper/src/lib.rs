use backend::{KoalaBear, integers::QuotientMap};
use leansig::{
    inc_encoding::target_sum::TargetSumEncoding,
    signature::{
        SignatureScheme,
        generalized_xmss::{
            GeneralizedXMSSPublicKey, GeneralizedXMSSSecretKey, GeneralizedXMSSSignature,
            GeneralizedXMSSSignatureScheme,
        },
    },
    symmetric::{
        message_hash::aborting::AbortingHypercubeMessageHash, prf::shake_to_field::ShakePRFtoF,
        tweak_hash::poseidon::PoseidonTweakHash,
    },
};
use leansig_fast_keygen::{signature::SignatureScheme as FastKeyGenSignatureScheme, symmetric::message_hash::encode_message};
use p3_field::PrimeField32;
use std::array;

#[cfg(feature = "test-config")]
pub const V: usize = 4;
#[cfg(not(feature = "test-config"))]
pub const V: usize = 46;
pub const BASE: usize = 1 << W;
const Z: usize = 8;
const Q: usize = 127;
#[cfg(feature = "test-config")]
pub const TARGET_SUM: usize = 6;
#[cfg(not(feature = "test-config"))]
pub const TARGET_SUM: usize = 200;
pub const RAND_LEN_FE: usize = 7;
pub const HASH_LEN_FE: usize = 8;
pub const MSG_LEN_FE: usize = 9;
pub const PARAMETER_LEN: usize = 5;
pub const TWEAK_LEN_FE: usize = 2;

pub const W: usize = 3;
pub const MESSAGE_LENGTH: usize = 32;
pub const POSEIDON24_CAPACITY: usize = 9;
pub const POSEIDON24_RATE: usize = 15;

#[cfg(feature = "test-config")]
pub const LOG_LIFETIME: usize = 8;
#[cfg(not(feature = "test-config"))]
pub const LOG_LIFETIME: usize = 32;

pub const SIG_SIZE_FE: usize = RAND_LEN_FE + (V + LOG_LIFETIME) * HASH_LEN_FE;

pub(crate) type F = KoalaBear;

#[cfg(feature = "test-config")]
pub const WOTS_PUBKET_SPONGE_DOMAIN_SEP: [F; POSEIDON24_CAPACITY] = F::new_array([
    627826400, 1244476188, 370678638, 978729783, 1996000804, 1380088873, 1753334201, 433326939, 1294775677,
]);
#[cfg(not(feature = "test-config"))]
pub const WOTS_PUBKET_SPONGE_DOMAIN_SEP: [F; POSEIDON24_CAPACITY] = F::new_array([
    2060061975, 916902315, 229801915, 83751504, 2093549181, 1743125625, 721042244, 1252069948, 1192880636,
]);

pub use leansig::symmetric::tweak_hash::TweakableHash;
use rand::CryptoRng;

pub type LeanSigTH = PoseidonTweakHash<PARAMETER_LEN, HASH_LEN_FE, TWEAK_LEN_FE, POSEIDON24_CAPACITY, V>;

type MH =
    AbortingHypercubeMessageHash<PARAMETER_LEN, RAND_LEN_FE, HASH_LEN_FE, V, BASE, Z, Q, TWEAK_LEN_FE, MSG_LEN_FE>;
type TH = PoseidonTweakHash<PARAMETER_LEN, HASH_LEN_FE, TWEAK_LEN_FE, POSEIDON24_CAPACITY, V>;
type PrF = ShakePRFtoF<HASH_LEN_FE, RAND_LEN_FE>;
type IE = TargetSumEncoding<MH, TARGET_SUM>;

pub type LeanSigScheme = GeneralizedXMSSSignatureScheme<PrF, IE, TH, LOG_LIFETIME>;
pub type XmssPublicKey = GeneralizedXMSSPublicKey<TH>;
pub type XmssSecretKey = GeneralizedXMSSSecretKey<PrF, IE, TH, LOG_LIFETIME>;
pub type XmssSignature = GeneralizedXMSSSignature<IE, TH>;

#[cfg(feature = "test-config")]
pub type FastKeyGenScheme = leansig_fast_keygen::signature::generalized_xmss::instantiations_aborting::lifetime_2_to_the_8::SchemeAbortingTargetSumLifetime8Dim46Base8;
#[cfg(feature = "test-config")]
pub type FastKeyGenSecretKey = leansig_fast_keygen::signature::generalized_xmss::instantiations_aborting::lifetime_2_to_the_8::SecretKeyAbortingTargetSumLifetime8Dim46Base8;
#[cfg(not(feature = "test-config"))]
pub type FastKeyGenScheme = leansig_fast_keygen::signature::generalized_xmss::instantiations_aborting::lifetime_2_to_the_32::SchemeAbortingTargetSumLifetime32Dim46Base8;
#[cfg(not(feature = "test-config"))]
pub type FastKeyGenSecretKey = leansig_fast_keygen::signature::generalized_xmss::instantiations_aborting::lifetime_2_to_the_32::SecretKeyAbortingTargetSumLifetime32Dim46Base8;

pub fn pubkey_merkle_root(pub_keys: &XmssPublicKey) -> [F; HASH_LEN_FE] {
    assert_eq!(pub_keys.root().len(), HASH_LEN_FE);
    array::from_fn(|i| F::from_canonical_checked(pub_keys.root()[i].as_canonical_u32()).unwrap())
}

pub fn pubkey_public_parameter(pub_keys: &XmssPublicKey) -> [F; PARAMETER_LEN] {
    assert_eq!(pub_keys.parameter().len(), PARAMETER_LEN);
    array::from_fn(|i| F::from_canonical_checked(pub_keys.parameter()[i].as_canonical_u32()).unwrap())
}

pub fn chain_tweak(slot: u32, chain_idx: u32, step: u32) -> [F; TWEAK_LEN_FE] {
    let [t0, t1] = LeanSigTH::chain_tweak(slot, chain_idx as u8, step as u8).to_field_elements();
    [
        F::from_canonical_checked(t0.as_canonical_u32()).unwrap(),
        F::from_canonical_checked(t1.as_canonical_u32()).unwrap(),
    ]
}

pub fn merkle_tweak(level: usize, pos_in_level: u32) -> [F; TWEAK_LEN_FE] {
    let [t0, t1] = LeanSigTH::tree_tweak(level as u8, pos_in_level).to_field_elements();
    [
        F::from_canonical_checked(t0.as_canonical_u32()).unwrap(),
        F::from_canonical_checked(t1.as_canonical_u32()).unwrap(),
    ]
}

pub fn xmss_merkle_path(sig: &XmssSignature) -> &Vec<[F; HASH_LEN_FE]> {
    unsafe { std::mem::transmute(sig.path()) }
}

pub fn xmss_randomness(sig: &XmssSignature) -> &[F; RAND_LEN_FE] {
    unsafe { std::mem::transmute(sig.rho()) }
}

pub fn xmmss_revealed_chain_tips(sig: &XmssSignature) -> &Vec<[F; HASH_LEN_FE]> {
    unsafe { std::mem::transmute(sig.hashes()) }
}

#[allow(clippy::result_unit_err)]
pub fn xmss_public_key_from_ssz(bytes: &[u8]) -> Result<XmssPublicKey, ()> {
    use ssz::Decode;
    XmssPublicKey::from_ssz_bytes(bytes).map_err(|_| ())
}

pub fn xmss_public_key_to_ssz(pk: &XmssPublicKey) -> Vec<u8> {
    use ssz::Encode;
    pk.as_ssz_bytes()
}

#[allow(clippy::result_unit_err)]
pub fn xmss_signature_from_ssz(bytes: &[u8]) -> Result<XmssSignature, ()> {
    use ssz::Decode;
    XmssSignature::from_ssz_bytes(bytes).map_err(|_| ())
}

pub fn xmss_signature_to_ssz(sig: &XmssSignature) -> Vec<u8> {
    use ssz::Encode;
    sig.as_ssz_bytes()
}

#[allow(clippy::result_unit_err)]
pub fn xmss_verify(
    pk: &XmssPublicKey,
    slot: u32,
    message: &[u8; MESSAGE_LENGTH],
    sig: &XmssSignature,
) -> Result<(), ()> {
    if LeanSigScheme::verify(pk, slot, message, sig) {
        Ok(())
    } else {
        Err(())
    }
}

pub fn xmss_encode_message(message: &[u8; MESSAGE_LENGTH]) -> [F; MSG_LEN_FE] {
    let encoded = encode_message::<MSG_LEN_FE>(message);
    array::from_fn(|i| F::from_canonical_checked(encoded[i].as_canonical_u32()).unwrap())
}

pub fn xmss_keygen_fast<R: CryptoRng>(
    rng: &mut R,
    activation_epoch: u32,
    num_active_epochs: u32,
) -> (FastKeyGenSecretKey, XmssPublicKey) {
    let (pk, sk) = FastKeyGenScheme::key_gen(rng, activation_epoch as usize, num_active_epochs as usize);
    #[allow(clippy::missing_transmute_annotations)]
    let pk = unsafe { std::mem::transmute(pk) };
    (sk, pk)
}

#[allow(clippy::result_unit_err)]
pub fn xmss_sign_fast(
    sk: &FastKeyGenSecretKey,
    message: &[u8; MESSAGE_LENGTH],
    slot: u32,
) -> Result<XmssSignature, ()> {
    unsafe { std::mem::transmute(FastKeyGenScheme::sign(sk, slot, message).map_err(|_| ())?) }
}
