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
pub const NUM_BENCHMARK_SIGNERS: usize = 10000;

pub fn message_for_benchmark() -> [F; MESSAGE_LEN_FE] {
    std::array::from_fn(F::from_usize)
}

#[derive(Serialize, Deserialize)]
struct SignersCacheFile {
    slot: u32,
    message: Vec<F>,
    signatures: Vec<(XmssPublicKey, XmssSignature)>,
}

fn cache_path() -> PathBuf {
    let file = "benchmark_signers_cache.bin";
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(format!("../../target/{file}"))
}

fn compute_signer(index: usize) -> (XmssPublicKey, XmssSignature) {
    let mut rng = StdRng::seed_from_u64(index as u64);
    let key_start = BENCHMARK_SLOT;
    let key_end = BENCHMARK_SLOT + 1;
    let (sk, pk) = xmss_key_gen(rng.random(), key_start, key_end).unwrap();
    let sig = xmss_sign(&mut rng, &sk, &message_for_benchmark(), BENCHMARK_SLOT).unwrap();
    (pk, sig)
}

fn try_load_cache(path: &PathBuf, first_pubkey: &XmssPublicKey) -> Option<Vec<(XmssPublicKey, XmssSignature)>> {
    let data = fs::read(path).ok()?;
    let decompressed = lz4_flex::decompress_size_prepended(&data).ok()?;
    let cached: SignersCacheFile = postcard::from_bytes(&decompressed).ok()?;

    if cached.slot != BENCHMARK_SLOT {
        println!(
            "Cache slot {} does not match benchmark slot {}, recomputing...",
            cached.slot, BENCHMARK_SLOT
        );
        return None;
    }
    if cached.message != message_for_benchmark() {
        println!("Cache message does not match benchmark message, recomputing...");
        return None;
    }
    if cached.signatures.len() != NUM_BENCHMARK_SIGNERS {
        println!(
            "Cache contains {} signatures, expected {}, recomputing...",
            cached.signatures.len(),
            NUM_BENCHMARK_SIGNERS
        );
        return None;
    }
    if cached.signatures[0].0 != *first_pubkey {
        println!("Cache first public key does not match computed first public key, recomputing...");
        return None;
    }

    Some(cached.signatures)
}

fn gen_benchmark_signers_cache() -> Vec<(XmssPublicKey, XmssSignature)> {
    let path = cache_path();

    // Compute first signer; its pubkey is used to validate the cache
    let first_signer = compute_signer(0);

    if let Some(signers) = try_load_cache(&path, &first_signer.0) {
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
        slot: BENCHMARK_SLOT,
        message: message_for_benchmark().to_vec(),
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
fn test_signature_cache() {
    let signatures = get_benchmark_signatures();
    signatures.par_iter().enumerate().for_each(|(i, (pk, sig))| {
        xmss_verify(pk, &message_for_benchmark(), sig, BENCHMARK_SLOT)
            .unwrap_or_else(|_| panic!("Signature {} failed to verify", i));
    });
}
