//! Minimal reproducer for the zk-alloc / WHIR-commit-FFT bug.
//!
//! Run:
//!
//!     cargo run --release --bin zk_alloc_bug_mre
//!
//! Expected: panic with `InvalidProof`.
//!
//! Run with the system allocator instead and the bug disappears:
//!
//!     cargo run --release --features standard-alloc --bin zk_alloc_bug_mre
//!
//! ## Trigger
//!
//! Three sequential `run_aggregation_benchmark` calls, each in its own
//! `begin_phase`/`end_phase` cycle:
//!
//!   1. one "warmup" leaf proof of ≥ ~900 signatures,
//!   2. an aggregation proof (any `n_recursions ≥ 1`, e.g. one 700-sig child),
//!   3. a "large" leaf proof of 1400 sigs at R=1/4 (which uses fft_len = 2^23,
//!      stacked_n_vars = 28 — i.e. close to the maximum the WHIR config supports).
//!
//! Removing **any** of the three steps makes the panic disappear:
//!  - warmup-only + leaf:                   OK
//!  - agg-only + leaf:                      OK
//!  - 4 sequential leaf proofs + leaf:      OK
//!  - 2 sequential aggs + leaf:             OK
//!  - warmup of 800 sigs (instead of ≥900): OK
//!
//! ## What the prover does wrong
//!
//! With debug instrumentation on `prove_execution.rs` and `whir/src/dft.rs`,
//! the divergence localises to one place. For step 3:
//!
//!  - public_input, bytecode hash, dims, stacked global polynomial bytes,
//!    commit-stage `prepared_evals` bytes, and the precomputed twiddles bytes
//!    are all *bit-identical* between a known-good standalone run and this
//!    failing run.
//!  - `dft_batch_by_evals`'s output then **diverges**: every run produces a
//!    different `mat.values` hash for the *same* input matrix. Specifically,
//!    after `par_initial_layers` and `dft_layer_par_extra_layers` everything
//!    still matches; the divergence first appears at the second iteration of
//!    the `dft_layer_par_triple` loop.
//!  - The same FFT call is fully deterministic across runs when built with
//!    `--features standard-alloc`.
//!  - It is also non-deterministic with `RAYON_NUM_THREADS=1`, so it is *not*
//!    a thread race.
//!  - Forcing every `arena_alloc_cold`/`alloc()` path (including the System
//!    fallback for slab spillover) to memset-zero the returned buffer
//!    *does not* fix it, so it is also *not* a stale-uninitialised-read.
//!
//! The remaining strong hypothesis is that something in `dft_layer_par_triple`
//! (or the SIMD `apply_to_rows`/`pack_slice_with_suffix_mut` cast it uses)
//! reads or writes in a way that depends on the relative virtual-address
//! layout of the chunks in `mat.values` — a layout that changes when some
//! allocations live on the arena slab and others spill to System.alloc, but
//! not when all allocations come from the same allocator.

use rec_aggregation::{AggregationTopology, benchmark::run_aggregation_benchmark};

#[cfg(not(feature = "standard-alloc"))]
#[global_allocator]
static ALLOC: zk_alloc::ZkAllocator = zk_alloc::ZkAllocator;

fn leaf(raw: usize, log_inv_rate: usize) -> AggregationTopology {
    AggregationTopology {
        raw_xmss: raw,
        children: vec![],
        log_inv_rate,
        overlap: 0,
    }
}

fn main() {
    #[cfg(not(feature = "standard-alloc"))]
    zk_alloc::init();

    let warmup = leaf(1400, 1);
    let agg_one_child = AggregationTopology {
        raw_xmss: 0,
        children: vec![leaf(700, 2)],
        log_inv_rate: 2,
        overlap: 0,
    };
    let target = leaf(1400, 2);

    eprintln!("[MRE] step 1: warmup leaf proof");
    let _ = run_aggregation_benchmark(&warmup, false, true);

    eprintln!("[MRE] step 2: aggregation proof (1 child)");
    let _ = run_aggregation_benchmark(&agg_one_child, false, true);

    eprintln!("[MRE] step 3: large leaf proof (1400 sigs R=1/4) — panics here under arena");
    let _ = run_aggregation_benchmark(&target, false, true);

    eprintln!("[MRE] all three steps completed without panic");
}
