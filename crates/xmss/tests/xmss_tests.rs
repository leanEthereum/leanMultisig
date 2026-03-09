use backend::*;
use rand::{SeedableRng, rngs::StdRng};
use xmss::*;

type F = KoalaBear;

#[test]
fn test_xmss_serialize_deserialize() {
    let keygen_seed: [u8; 32] = std::array::from_fn(|i| i as u8);
    let message: [F; MESSAGE_LEN_FE] = std::array::from_fn(|i| F::from_usize(i * 3 + 7));

    let (sk, pk) = xmss_key_gen(keygen_seed, 100, 115).unwrap();
    let sig = xmss_sign(&mut StdRng::seed_from_u64(100), &sk, &message, 100).unwrap();

    let pk_bytes = postcard::to_allocvec(&pk).unwrap();
    let pk2: XmssPublicKey = postcard::from_bytes(&pk_bytes).unwrap();
    assert_eq!(pk, pk2);

    let sig_bytes = postcard::to_allocvec(&sig).unwrap();
    let sig2: XmssSignature = postcard::from_bytes(&sig_bytes).unwrap();
    assert_eq!(sig, sig2);

    xmss_verify(&pk2, &message, &sig2).unwrap();
}

#[test]
fn keygen_sign_verify() {
    let keygen_seed: [u8; 32] = std::array::from_fn(|i| i as u8);
    let message: [F; MESSAGE_LEN_FE] = std::array::from_fn(|i| F::from_usize(i * 3 + 7));

    for slot in [0, 1234, u32::MAX] {
        let (sk, pk) = xmss_key_gen(keygen_seed, slot.saturating_sub(1), slot.saturating_add(2)).unwrap();
        let sig = xmss_sign(&mut StdRng::seed_from_u64(slot as u64), &sk, &message, slot).unwrap();
        xmss_verify(&pk, &message, &sig).unwrap();
    }
}

#[test]
#[ignore]
fn encoding_grinding_bits() {
    let n = 100;
    let xmss_pub_key = XmssPublicKey {
        merkle_root: Default::default(),
        public_param: Default::default(),
    };
    let total_iters = (0..n)
        .into_par_iter()
        .map(|i| {
            let message: [F; MESSAGE_LEN_FE] = Default::default();
            let slot = i as u32;
            let mut rng = StdRng::seed_from_u64(i as u64);
            let (_randomness, _encoding, num_iters) =
                find_randomness_for_wots_encoding(&message, slot, &xmss_pub_key, &mut rng);
            num_iters
        })
        .sum::<usize>();
    let grinding = ((total_iters as f64) / (n as f64)).log2();
    println!("Average grinding bits: {:.1}", grinding);
}
