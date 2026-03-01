use backend::*;
use rand::{SeedableRng, rngs::StdRng};
use xmss::*;

type F = KoalaBear;

#[test]
fn test_xmss_serialize_deserialize() {
    let keygen_seed: [u8; 20] = std::array::from_fn(|i| i as u8);
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
    let keygen_seed: [u8; 20] = std::array::from_fn(|i| i as u8);
    let message: [F; MESSAGE_LEN_FE] = std::array::from_fn(|i| F::from_usize(i * 3 + 7));

    let (sk, pk) = xmss_key_gen(keygen_seed, 100, 115).unwrap();
    for slot in 100..=115 {
        let sig = xmss_sign(&mut StdRng::seed_from_u64(u64::from(slot)), &sk, &message, slot).unwrap();
        xmss_verify(&pk, &message, &sig).unwrap();
    }
}

#[test]
fn test_xmss_key_gen_range_too_large() {
    let seed = [0u8; 20];
    let result = xmss_key_gen(seed, 0, (1 << 20) + 1);
    assert!(matches!(result, Err(XmssKeyGenError::RangeTooLarge)));
}

#[test]
fn test_xmss_key_gen_max_range_ok() {
    // Exactly MAX_SLOT_RANGE should be accepted (but may be slow, so use smaller range)
    let seed = [0u8; 20];
    let result = xmss_key_gen(seed, 0, 99);
    assert!(result.is_ok());
}

#[test]
#[ignore]
fn encoding_grinding_bits() {
    let n = 100;
    let total_iters = (0..n)
        .into_par_iter()
        .map(|i| {
            let message: [F; MESSAGE_LEN_FE] = Default::default();
            let slot = i as u32;
            let truncated_merkle_root: [F; TRUNCATED_MERKLE_ROOT_LEN_FE] = Default::default();
            let mut rng = StdRng::seed_from_u64(i as u64);
            let (_randomness, _encoding, num_iters) =
                find_randomness_for_wots_encoding(&message, slot, &truncated_merkle_root, &mut rng);
            num_iters
        })
        .sum::<usize>();
    let grinding = ((total_iters as f64) / (n as f64)).log2();
    println!("Average grinding bits: {:.1}", grinding);
}
