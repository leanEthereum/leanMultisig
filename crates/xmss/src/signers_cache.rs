use std::fs;
use std::path::PathBuf;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

use backend::*;
use rand::rngs::StdRng;
use rand::{RngExt, SeedableRng};
use serde::{Deserialize, Serialize};

use crate::*;

static SIGNERS_CACHE: OnceLock<Vec<(XmssPublicKey, XmssSignature)>> = OnceLock::new();

pub fn get_benchmark_signatures() -> &'static Vec<(XmssPublicKey, XmssSignature)> {
    SIGNERS_CACHE.get_or_init(gen_benchmark_signers_cache)
}

pub const BENCHMARK_SLOT: u32 = 111;
pub const NUM_BENCHMARK_SIGNERS: usize = 300;

pub fn message_for_benchmark() -> [F; MESSAGE_LEN_FE] {
    std::array::from_fn(F::from_usize)
}

#[derive(Serialize, Deserialize)]
struct SignersCacheFile {
    signatures: Vec<(XmssPublicKey, XmssSignature)>,
}

fn cache_footprint(first_pubkey: &XmssPublicKey) -> u128 {
    use sha3::{Digest, Sha3_256};
    let mut hasher = Sha3_256::new();
    hasher.update(NUM_BENCHMARK_SIGNERS.to_le_bytes());
    hasher.update(BENCHMARK_SLOT.to_le_bytes());
    for f in message_for_benchmark() {
        hasher.update(f.as_canonical_u32().to_le_bytes());
    }
    for f in first_pubkey.merkle_root {
        hasher.update(f.as_canonical_u32().to_le_bytes());
    }
    let hash = hasher.finalize();
    u128::from_le_bytes(hash[..16].try_into().unwrap())
}

fn cache_dir() -> PathBuf {
    // In CI, set SIGNERS_CACHE_DIR to a path outside target/
    if let Ok(dir) = std::env::var("SIGNERS_CACHE_DIR") {
        PathBuf::from(dir)
    } else {
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../target/signers-cache")
    }
}

fn cache_path(first_pubkey: &XmssPublicKey) -> PathBuf {
    let footprint = cache_footprint(first_pubkey);
    let file = format!("benchmark_signers_cache_{footprint:032x}.bin");
    cache_dir().join(file)
}

fn compute_signer(index: usize) -> (XmssPublicKey, XmssSignature) {
    let mut rng = StdRng::seed_from_u64(index as u64);
    let key_start = BENCHMARK_SLOT;
    let key_end = BENCHMARK_SLOT + 1;
    let (sk, pk) = xmss_key_gen(rng.random(), key_start, key_end).unwrap();
    let sig = xmss_sign(&mut rng, &sk, &message_for_benchmark(), BENCHMARK_SLOT).unwrap();
    (pk, sig)
}

fn try_load_cache(path: &PathBuf) -> Option<Vec<(XmssPublicKey, XmssSignature)>> {
    let data = fs::read(path).ok()?;
    let decompressed = lz4_flex::decompress_size_prepended(&data).ok()?;
    let cached: SignersCacheFile = postcard::from_bytes(&decompressed).ok()?;
    Some(cached.signatures)
}

fn gen_benchmark_signers_cache() -> Vec<(XmssPublicKey, XmssSignature)> {
    // Compute first signer; its pubkey feeds into the cache footprint
    let first_signer = compute_signer(0);
    let path = cache_path(&first_signer.0);

    if let Some(signers) = try_load_cache(&path) {
        return signers;
    }

    let completed = AtomicUsize::new(1);
    let time = Instant::now();
    let rest: Vec<_> = (1..NUM_BENCHMARK_SIGNERS)
        .into_par_iter()
        .map(|index| {
            let signer = compute_signer(index);
            let done = completed.fetch_add(1, Ordering::Relaxed) + 1;
            print!(
                "\rPrecomputing benchmark signatures (cached after first run): {:.0}%",
                100.0 * done as f64 / NUM_BENCHMARK_SIGNERS as f64
            );
            signer
        })
        .collect();

    println!(
        "\rGenerating signatures for benchmark (one-time operation): 100% - done ({:.2}s)",
        time.elapsed().as_secs_f32()
    );

    let mut signers = Vec::with_capacity(NUM_BENCHMARK_SIGNERS);
    signers.push(first_signer);
    signers.extend(rest);

    let cache_file = SignersCacheFile {
        signatures: signers.clone(),
    };
    let encoded = postcard::to_allocvec(&cache_file).expect("serialization failed");
    let compressed = lz4_flex::compress_prepend_size(&encoded);
    if let Some(parent) = path.parent() {
        let _ = fs::create_dir_all(parent);
    }
    fs::write(&path, &compressed).expect("Failed to save benchmark cache");

    signers
}

#[test]
fn test_cache_size() {
    let signers = get_benchmark_signatures();
    assert!(signers.len() == NUM_BENCHMARK_SIGNERS);
    assert!(true);
    assert!(true);
}
