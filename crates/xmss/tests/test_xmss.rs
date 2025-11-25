use p3_koala_bear::KoalaBear;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use xmss::*;

type F = KoalaBear;
const LOG_LIFETIME: usize = 5;
const FIRST_SLOT: usize = 7855;
const SIGNATURE_SLOT: usize = FIRST_SLOT + (1 << LOG_LIFETIME) / 3;

#[test]
fn test_wots_signature() {
    let mut rng = StdRng::seed_from_u64(0);
    let sk = WotsSecretKey::random(&mut rng);
    let message_hash: [F; 8] = rng.random();
    let signature = sk.sign(&message_hash, &mut rng);
    assert_eq!(
        signature.recover_public_key(&message_hash, &signature,).unwrap(),
        *sk.public_key()
    );
}

#[test]
fn test_xmss_signature() {
    let mut rng = StdRng::seed_from_u64(0);
    let sk = XmssSecretKey::random(&mut rng, FIRST_SLOT, LOG_LIFETIME);
    let message_hash: [F; 8] = rng.random();
    let slot = rng.random_range(FIRST_SLOT..(FIRST_SLOT + (1 << LOG_LIFETIME)));
    let signature = sk.sign(&message_hash, slot, &mut rng).unwrap();
    let public_key = sk.public_key();
    assert!(public_key.verify(&message_hash, &signature).is_some());
}

#[test]
fn test_phony_xmss_signature() {
    let mut rng = StdRng::seed_from_u64(0);
    let sk = PhonyXmssSecretKey::random(&mut rng, FIRST_SLOT, LOG_LIFETIME, SIGNATURE_SLOT);
    let message_hash: [F; 8] = rng.random();
    let signature = sk.sign(&message_hash, &mut rng);
    assert!(sk.public_key.verify(&message_hash, &signature).is_some());
}
