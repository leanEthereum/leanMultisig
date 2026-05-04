//! Minimal reproducer for the zk-alloc / FFT non-determinism bug.
//!
//! Run:
//!
//!     cargo run --release --bin zk_alloc_bug_mre
//!
//! Expected (with default zk-alloc):
//!
//!     panicked at ... InvalidProof
//!
//! Run with the system allocator instead and the bug disappears:
//!
//!     cargo run --release --features standard-alloc --bin zk_alloc_bug_mre
//!
//! Summary of the bug:
//!
//! 1. After running a `1400 R=1/2` proof (warmup) followed by an aggregation
//!    of two `700 R=1/4` proofs, generating a `1400 R=1/4` *leaf* proof
//!    produces an invalid proof — the immediate verify (= the same machinery
//!    `verify_execution`) rejects it.
//! 2. The bug is single-thread reproducible (`RAYON_NUM_THREADS=1`).
//! 3. With `--features standard-alloc` the same code path produces a valid
//!    proof.
//! 4. Tracing the prover step-by-step shows divergence in the WHIR commit
//!    FFT: `dft_layer_par_triple` produces *different* `mat.values` across
//!    runs given **identical** input (same hash) and twiddles (same hash).
//!    With `standard-alloc` the FFT output is bit-identical across runs.

use rec_aggregation::{AggregationTopology, benchmark::run_aggregation_benchmark};

#[cfg(not(feature = "standard-alloc"))]
#[global_allocator]
static ALLOC: zk_alloc::ZkAllocator = zk_alloc::ZkAllocator;

fn main() {
    #[cfg(not(feature = "standard-alloc"))]
    zk_alloc::init();

    let leaf = |raw: usize, log_inv_rate: usize| AggregationTopology {
        raw_xmss: raw,
        children: vec![],
        log_inv_rate,
        overlap: 0,
    };

    let warmup_1400_r2 = leaf(1400, 1);
    let agg_700_700_r4 = AggregationTopology {
        raw_xmss: 0,
        children: vec![leaf(700, 2), leaf(700, 2)],
        log_inv_rate: 2,
        overlap: 0,
    };
    let leaf_1400_r4 = leaf(1400, 2);

    eprintln!("[MRE] step 1: warmup proof (1400 sigs, R=1/2)");
    let _ = run_aggregation_benchmark(&warmup_1400_r2, false, true);

    eprintln!("[MRE] step 2: aggregation proof (700+700 → 1400 sigs, R=1/4)");
    let _ = run_aggregation_benchmark(&agg_700_700_r4, false, true);

    eprintln!("[MRE] step 3: leaf proof (1400 sigs, R=1/4) — panics with arena, OK with standard-alloc");
    let _ = run_aggregation_benchmark(&leaf_1400_r4, false, true);

    eprintln!("[MRE] all three steps completed without panic");
}
