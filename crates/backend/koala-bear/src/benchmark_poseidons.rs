use std::hint::black_box;
use std::time::Instant;

use field::Field;
use field::PackedValue;
use field::PrimeCharacteristicRing;
use rayon::prelude::*;

use crate::{KoalaBear, default_koalabear_poseidon1_16};

type FPacking = <KoalaBear as Field>::Packing;
const PACKING_WIDTH: usize = <FPacking as PackedValue>::WIDTH;

/// Benchmark Poseidon1-16 compression throughput.
///
/// By default this measures the CPU SIMD path. Setting `BENCH_GPU=1` switches to
/// the Metal GPU backend (`gpu-poseidon`) on macOS — useful for direct
/// CPU-vs-GPU comparisons of the raw permutation throughput.
///
/// Run:
///   cargo test --release --package mt-koala-bear --lib -- benchmark_poseidons::bench_poseidon --exact --nocapture --ignored
///   BENCH_GPU=1 cargo test --release --package mt-koala-bear --lib -- benchmark_poseidons::bench_poseidon --exact --nocapture --ignored
#[test]
#[ignore]
fn bench_poseidon() {
    let use_gpu = std::env::var("BENCH_GPU").is_ok_and(|v| v != "0" && !v.is_empty());

    if use_gpu {
        bench_poseidon_gpu();
    } else {
        bench_poseidon_cpu();
    }
}

fn bench_poseidon_cpu() {
    let n = 1 << 25;
    let poseidon1_16 = default_koalabear_poseidon1_16();
    let n_threads = rayon::current_num_threads();

    // Each rayon task owns its own state and runs a chunk of compressions in a
    // tight SIMD loop. The total compression count across threads is `n`.
    let chunks_per_thread = (n / PACKING_WIDTH).div_ceil(n_threads);

    // Warmup so caches/branch predictors are settled.
    let _ = (0..n_threads)
        .into_par_iter()
        .map(|_| {
            let mut state: [FPacking; 16] = [FPacking::ZERO; 16];
            for _ in 0..1 << 12 {
                poseidon1_16.compress_in_place(&mut state);
            }
            state[0]
        })
        .collect::<Vec<_>>();

    let time = Instant::now();
    let sink: Vec<FPacking> = (0..n_threads)
        .into_par_iter()
        .map(|_| {
            let mut state: [FPacking; 16] = [FPacking::ZERO; 16];
            for _ in 0..chunks_per_thread {
                poseidon1_16.compress_in_place(&mut state);
            }
            state[0]
        })
        .collect();
    let _ = black_box(sink);
    let time_p1_simd = time.elapsed();

    let total_hashes = n_threads * chunks_per_thread * PACKING_WIDTH;
    let total_per_sec = total_hashes as f64 / time_p1_simd.as_secs_f64() / 1_000_000.0;
    let per_core_per_sec = total_per_sec / n_threads as f64;
    println!(
        "Poseidon1 16 CPU SIMD (width {}, {} threads): {:.2}M hashes/s total = {:.2}M/s per core ({:?} for {} hashes)",
        PACKING_WIDTH, n_threads, total_per_sec, per_core_per_sec, time_p1_simd, total_hashes,
    );
}

fn bench_poseidon_gpu() {
    if !gpu_poseidon::metal_available() {
        println!("GPU backend unavailable; falling back to CPU bench.");
        bench_poseidon_cpu();
        return;
    }

    // Total compressions ≈ 2^23. We let each GPU thread chain many compressions
    // so dispatch/scheduling overhead is amortized — otherwise the GPU spends
    // most of its time launching threads instead of computing.
    let n_threads = 1 << 16; // 65,536 threads
    let n_iter: u32 = 128; // 128 compressions per thread → 2^23 total

    // Warmup so MSL compile + pipeline creation + caches aren't counted.
    let _ = black_box(gpu_poseidon::bench_compress_chain(1 << 12, 8));

    let (elapsed, total) = gpu_poseidon::bench_compress_chain(n_threads, n_iter);
    let _ = black_box(total);
    println!(
        "Poseidon1 16 GPU (Metal, {} threads x {} iter): {:.2}M hashes/s ({:?} for {} hashes)",
        n_threads,
        n_iter,
        total as f64 / elapsed.as_secs_f64() / 1_000_000.0,
        elapsed,
        total,
    );
}
