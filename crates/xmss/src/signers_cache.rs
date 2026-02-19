use std::path::PathBuf;

use backend::*;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

use crate::*;

pub const BENCHMARK_SLOT: u32 = 1111;

pub fn message_for_benchmark() -> [F; MESSAGE_LEN_FE] {
    std::array::from_fn(F::from_usize)
}

fn benchmark_keygen<R: Rng>(rng: &mut R) -> (XmssSecretKey, XmssPublicKey) {
    let key_start = BENCHMARK_SLOT - rng.random_range(0..3);
    let key_end = BENCHMARK_SLOT + rng.random_range(1..3);
    xmss_key_gen(rng.random(), key_start, key_end).unwrap()
}

pub fn find_randomness_for_benchmark(index: usize) -> [F; RANDOMNESS_LEN_FE] {
    let message = message_for_benchmark();
    let mut rng = StdRng::seed_from_u64(index as u64);
    let (_sk, pk) = benchmark_keygen(&mut rng);
    let truncated: [F; TRUNCATED_MERKLE_ROOT_LEN_FE] =
        pk.merkle_root[..TRUNCATED_MERKLE_ROOT_LEN_FE].try_into().unwrap();
    let (randomness, _, _) = find_randomness_for_wots_encoding(&message, BENCHMARK_SLOT, &truncated, &mut rng);
    randomness
}

/// Reconstruct a benchmark signer's public key and signature from its index
/// and pre-computed WOTS randomness.
pub fn reconstruct_signer_for_benchmark(
    index: usize,
    randomness: [F; RANDOMNESS_LEN_FE],
) -> (XmssPublicKey, XmssSignature) {
    let message = message_for_benchmark();
    let mut rng = StdRng::seed_from_u64(index as u64);
    let (sk, pk) = benchmark_keygen(&mut rng);
    let sig = xmss_sign_with_randomness(&sk, &message, BENCHMARK_SLOT, randomness).unwrap();
    (pk, sig)
}

fn cache_file_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("test_data/benchmark_signers.json")
}

pub fn write_benchmark_signers_cache(randomnesses: &[[F; RANDOMNESS_LEN_FE]]) {
    let path = cache_file_path();
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent).unwrap();
    }
    let json = format!(
        "[{}]",
        randomnesses
            .iter()
            .flat_map(|r| r.iter().map(|f| f.to_string()))
            .collect::<Vec<_>>()
            .join(",")
    );
    std::fs::write(&path, json).unwrap();
    println!("Wrote {} entries to {}", randomnesses.len(), path.display());
}

pub fn read_benchmark_signers_cache() -> Vec<[F; RANDOMNESS_LEN_FE]> {
    let path = cache_file_path();
    let text = std::fs::read_to_string(&path).unwrap_or_else(|_| {
        panic!(
            "cache not found at {}, run generate_benchmark_signers_cache",
            path.display()
        )
    });
    let text = text.trim();
    let inner = text.strip_prefix('[').unwrap().strip_suffix(']').unwrap();
    let values: Vec<u32> = inner
        .split(',')
        .map(|s| s.trim().parse().expect("invalid value in cache"))
        .collect();
    assert!(values.len().is_multiple_of(RANDOMNESS_LEN_FE));
    values
        .chunks_exact(RANDOMNESS_LEN_FE)
        .map(|chunk| std::array::from_fn(|i| F::from_u32(chunk[i])))
        .collect()
}

#[test]
#[ignore]
fn generate_benchmark_signers_cache() {
    use std::time::Instant;
    let n_signers = 10_000;

    println!("Finding WOTS randomness for {} signers...", n_signers);
    let start = Instant::now();
    let randomnesses: Vec<[F; RANDOMNESS_LEN_FE]> = (0..n_signers)
        .into_par_iter()
        .map(find_randomness_for_benchmark)
        .collect();
    println!("Done in {:.1}s", start.elapsed().as_secs_f64());

    write_benchmark_signers_cache(&randomnesses);

    let message = message_for_benchmark();
    for &i in &[0, 1, n_signers / 2, n_signers - 1] {
        let (pk, sig) = reconstruct_signer_for_benchmark(i, randomnesses[i]);
        xmss_verify(&pk, &message, &sig).unwrap();
    }
}

#[test]
fn test_benchmark_signers_cache() {
    let cache = read_benchmark_signers_cache();
    let message = message_for_benchmark();
    for &i in &[0, 1, 2, cache.len() / 2, cache.len() - 1] {
        let (pk, sig) = reconstruct_signer_for_benchmark(i, cache[i]);
        xmss_verify(&pk, &message, &sig).unwrap();
    }
}
