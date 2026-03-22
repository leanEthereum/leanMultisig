use std::sync::OnceLock;

use backend::*;
use rand::rngs::StdRng;
use rand::{RngExt, SeedableRng};

use crate::*;

static SIGNERS_CACHE: OnceLock<Vec<(XmssPublicKey, XmssSignature)>> = OnceLock::new();

pub fn get_benchmark_signers_cache() -> &'static Vec<(XmssPublicKey, XmssSignature)> {
    SIGNERS_CACHE.get_or_init(gen_benchmark_signers_cache)
}

pub const BENCHMARK_SLOT: u32 = 1111;
pub const BENCHMARK_MESSAGE: [u8; MESSAGE_LENGTH] = [
    78, 32, 21, 11, 1, 76, 255, 254, 0, 0, 22, 11, 11, 87, 87, 32, 11, 32, 11, 76, 23, 12, 11, 2, 2, 2, 2, 2, 2, 3, 4,
    5,
];
pub const NUM_BENCHMARK_SIGNERS: usize = 10000;

fn gen_benchmark_signers_cache() -> Vec<(XmssPublicKey, XmssSignature)> {
    (0..NUM_BENCHMARK_SIGNERS)
        .into_par_iter()
        .map(|index| {
            let mut rng = StdRng::seed_from_u64(index as u64);
            let key_start = BENCHMARK_SLOT - rng.random_range(0..3);
            let key_end = BENCHMARK_SLOT + rng.random_range(1..3);
            let (sk, pk) = xmss_keygen(&mut rng, key_start, key_end);
            let sig = xmss_sign(&sk, &BENCHMARK_MESSAGE, BENCHMARK_SLOT).unwrap();
            (pk, sig)
        })
        .collect()
}
