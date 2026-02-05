use multilinear_toolkit::prelude::*;
use p3_koala_bear::KoalaBear;
use rand::{SeedableRng, rngs::StdRng};
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

#[test]
#[ignore]
fn encoding_grinding_bits() {
    let n = 1000;
    let total_iters = (0..10_000)
        .into_par_iter()
        .map(|i| {
            let message: [F; 8] = Default::default();
            let epoch = i as u32;
            let truncated_merkle_root: [F; 6] = Default::default();
            let mut rng = StdRng::seed_from_u64(i as u64);
            let (_randomness, _encoding, num_iters) =
                find_randomness_for_wots_encoding(&message, epoch, &truncated_merkle_root, &mut rng);
            num_iters
        })
        .sum::<usize>();
    let grinding = ((total_iters as f64) / (n as f64)).log2();
    println!("Average grinding bits: {:.1}", grinding);
}
