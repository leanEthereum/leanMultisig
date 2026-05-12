//! Workload-aware heuristics for `ExecutionHints` used by the aggregation prover.
//!
//! The aggregation program's runtime cost (cycle count, memory cells touched, per-table row
//! counts) scales roughly linearly with the number of raw XMSS signatures verified directly and
//! the number of sub-proofs verified recursively. The constants below come from measurements on
//! a handful of `xmss` / `recursion` benchmark configurations.
//!
//! `prove_execution_hinted` handles both directions of error: an under-estimate is caught via a
//! `SlotColumn` overflow panic and falls back to a dry-run; an over-estimate is detected after the
//! trial execution (before the heavy commit/sumcheck/WHIR phases) and triggers a re-execution
//! with tight hints. Either way the prover still produces a valid proof — only the time cost is
//! affected. Both retries emit an `eprintln` + `tracing::warn` with both the supplied hint and
//! the actual sizes so these constants can be tuned over time.

use backend::log2_ceil_usize;
use lean_vm::{ExecutionHints, MIN_LOG_MEMORY_SIZE, MIN_LOG_N_ROWS_PER_TABLE, Table};
use std::collections::BTreeMap;

/// Per-raw-XMSS-signature costs. Measured against `xmss --n-signatures {100, 500, 1000, 1400}`
/// and the inner aggregation of `recursion --n 1` (775 raw XMSS): ~650 cycles, ~2400 memory
/// cells, ~20 extension-op rows, ~170 poseidon-16 rows per signature.
const CYCLES_PER_XMSS: usize = 700;
const MEMORY_PER_XMSS: usize = 2700;
const EXTENSION_OP_PER_XMSS: usize = 25;
const POSEIDON_PER_XMSS: usize = 180;

/// Per-recursive-sub-proof costs (verifier-side WHIR + sumcheck + Fiat-Shamir replay). Measured
/// against the outer aggregation of `recursion --n 1` (1 recursion, 0 raw XMSS): ~110k cycles,
/// ~285k memory cells, ~45k extension-op rows, ~10k poseidon-16 rows.
const CYCLES_PER_RECURSION: usize = 120_000;
const MEMORY_PER_RECURSION: usize = 320_000;
const EXTENSION_OP_PER_RECURSION: usize = 50_000;
const POSEIDON_PER_RECURSION: usize = 12_000;

/// Fixed program overhead (preamble, public-input absorbing, etc.).
const BASE_CYCLES: usize = 30_000;
const BASE_MEMORY: usize = 100_000;
const BASE_EXTENSION_OP: usize = 1_000;
const BASE_POSEIDON: usize = 2_000;

/// Multiplicative safety margin applied to every estimate. Tune downward to claim back peak
/// memory at the cost of more fallbacks; tune upward if a workload regularly under-estimates.
const SAFETY_MARGIN_PERCENT: usize = 15;

#[inline]
fn with_margin(x: usize) -> usize {
    x + x.saturating_mul(SAFETY_MARGIN_PERCENT) / 100
}

#[inline]
fn log_ceil_with_floor(x: usize, floor: usize) -> usize {
    log2_ceil_usize(x.max(1)).max(floor)
}

/// Compute an `ExecutionHints` for the unified aggregation program from the two workload knobs
/// the caller already has on hand: number of raw XMSS signatures verified directly, and number
/// of recursive sub-proofs verified.
pub fn aggregation_hints(n_xmss: usize, n_recursions: usize) -> ExecutionHints {
    let cycles = with_margin(BASE_CYCLES + CYCLES_PER_XMSS * n_xmss + CYCLES_PER_RECURSION * n_recursions);
    let memory = with_margin(BASE_MEMORY + MEMORY_PER_XMSS * n_xmss + MEMORY_PER_RECURSION * n_recursions);
    let ext_op =
        with_margin(BASE_EXTENSION_OP + EXTENSION_OP_PER_XMSS * n_xmss + EXTENSION_OP_PER_RECURSION * n_recursions);
    let poseidon = with_margin(BASE_POSEIDON + POSEIDON_PER_XMSS * n_xmss + POSEIDON_PER_RECURSION * n_recursions);

    let log_memory_size = log_ceil_with_floor(memory, MIN_LOG_MEMORY_SIZE);
    let log_exec = log_ceil_with_floor(cycles, MIN_LOG_N_ROWS_PER_TABLE);
    let log_ext_op = log_ceil_with_floor(ext_op, MIN_LOG_N_ROWS_PER_TABLE);
    let log_poseidon = log_ceil_with_floor(poseidon, MIN_LOG_N_ROWS_PER_TABLE);

    // The prover requires `memory >= execution table` and `execution table >= every other table`;
    // bump up if our independent estimates violate the ordering.
    let log_exec = log_exec.max(log_ext_op).max(log_poseidon);
    let log_memory_size = log_memory_size.max(log_exec);

    let mut tables_log_n_rows = BTreeMap::new();
    tables_log_n_rows.insert(Table::execution(), log_exec);
    tables_log_n_rows.insert(Table::extension_op(), log_ext_op);
    tables_log_n_rows.insert(Table::poseidon16(), log_poseidon);

    ExecutionHints {
        log_memory_size,
        tables_log_n_rows,
    }
}
