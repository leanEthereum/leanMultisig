use std::time::Instant;

use p3_koala_bear::KoalaBear;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use xmss::*;

type F = KoalaBear;

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
    let first_slot = 555;
    let log_lifetime: usize = std::env::var("XMSS_LOG_LIFETIME")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(5);
    let mut rng = StdRng::seed_from_u64(0);
    let seed: [u8; 32] = rng.random();
    let time = Instant::now();
    let sk = XmssSecretKey::new(seed, first_slot, log_lifetime);
    println!("XMSS keygen time: {:?}", time.elapsed());
    let message_hash: [F; 8] = rng.random();
    let slot = rng.random_range(first_slot..(first_slot + (1 << log_lifetime)));
    let signature = sk.sign(&message_hash, slot, &mut rng).unwrap();
    let public_key = sk.public_key();
    assert!(public_key.verify(&message_hash, &signature).is_some());
}
