use multilinear_toolkit::prelude::PrimeCharacteristicRing;
use p3_koala_bear::KoalaBear;
use xmss::*;

type F = KoalaBear;

#[test]
fn keygen_sign_verify() {
    let keygen_seed: [u8; 32] = std::array::from_fn(|i| i as u8);
    let randomness_seed: [u8; 32] = std::array::from_fn(|i| (i * 2 + 1) as u8);
    let message: [F; 8] = std::array::from_fn(|i| F::from_usize(i * 3 + 7));

    let (sk, pk) = xmss_key_gen(keygen_seed, 100, 115).unwrap();
    for slot in 100..=115 {
        let sig = xmss_sign(randomness_seed, &sk, &message, slot).unwrap();
        xmss_verify(&pk, &message, &sig).unwrap();
    }
}
