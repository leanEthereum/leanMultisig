use p3_koala_bear::KoalaBear;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use xmss::*;

type F = KoalaBear;
const LOG_LIFETIME: usize = 5;

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
    let sk = XmssSecretKey::<LOG_LIFETIME>::random(&mut rng);
    let message_hash: [F; 8] = rng.random();
    let index = rng.random_range(0..(1 << LOG_LIFETIME));
    let signature = sk.sign(&message_hash, index, &mut rng);
    let public_key = sk.public_key();
    assert!(public_key.verify(&message_hash, &signature).is_some());
}

#[test]
fn test_phony_xmss_signature() {
    let mut rng = StdRng::seed_from_u64(0);
    let sk = PhonyXmssSecretKey::<LOG_LIFETIME>::random(&mut rng, 6);
    let message_hash: [F; 8] = rng.random();
    let signature = sk.sign(&message_hash, &mut rng);
    assert!(sk.public_key.verify(&message_hash, &signature).is_some());
}
