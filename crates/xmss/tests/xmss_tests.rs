use multilinear_toolkit::prelude::*;
use p3_koala_bear::KoalaBear;
use rand::{SeedableRng, rngs::StdRng};
use xmss::*;

type F = KoalaBear;

#[test]
fn keygen_sign_verify() {
    let keygen_seed: [u8; 32] = std::array::from_fn(|i| i as u8);
    let message: [F; MESSAGE_LEN_FE] = std::array::from_fn(|i| F::from_usize(i * 3 + 7));

    let (sk, pk) = xmss_key_gen(keygen_seed, 100, 115).unwrap();
    for slot in 100..=115 {
        let sig = xmss_sign(&mut StdRng::seed_from_u64(slot as u64), &sk, &message, slot).unwrap();
        xmss_verify(&pk, &message, &sig).unwrap();
    }
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
