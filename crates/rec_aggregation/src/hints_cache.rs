//! On-disk cache of `ExecutionHints` measured from past runs.
//!
//! Layout: `<workspace>/target/lean_multisig_hints/<bytecode_hash>.json`. One file per zkDSL
//! bytecode (keyed by `Bytecode::hash`, so any change to the .py sources invalidates the cache).
//! Each file holds a JSON map `{"<n_xmss>:<n_recursions>": {log_memory, log_execution,
//! log_extension_op, log_poseidon16}}` — the tight, exact-fit hints produced by
//! `prove_execution_hinted`'s final attempt.
//!
//! On a cache hit the prover skips the heuristic + retry entirely. On a miss we fall back to the
//! workload heuristic and persist the actual sizes after proving.

use backend::PrimeField32;
use lean_vm::{ExecutionHints, F, Table};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::path::PathBuf;

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
struct CachedHints {
    log_memory: usize,
    log_execution: usize,
    log_extension_op: usize,
    log_poseidon16: usize,
}

impl From<&ExecutionHints> for CachedHints {
    fn from(h: &ExecutionHints) -> Self {
        Self {
            log_memory: h.log_memory_size,
            log_execution: h.tables_log_n_rows[&Table::execution()],
            log_extension_op: h.tables_log_n_rows[&Table::extension_op()],
            log_poseidon16: h.tables_log_n_rows[&Table::poseidon16()],
        }
    }
}

impl From<CachedHints> for ExecutionHints {
    fn from(c: CachedHints) -> Self {
        let mut tables_log_n_rows = BTreeMap::new();
        tables_log_n_rows.insert(Table::execution(), c.log_execution);
        tables_log_n_rows.insert(Table::extension_op(), c.log_extension_op);
        tables_log_n_rows.insert(Table::poseidon16(), c.log_poseidon16);
        Self {
            log_memory_size: c.log_memory,
            tables_log_n_rows,
        }
    }
}

fn hash_to_hex(bytecode_hash: &[F; 8]) -> String {
    let mut out = String::with_capacity(64);
    for f in bytecode_hash {
        out.push_str(&format!("{:08x}", f.as_canonical_u32()));
    }
    out
}

fn workload_key(n_xmss: usize, n_recursions: usize) -> String {
    format!("{n_xmss}:{n_recursions}")
}

fn cache_dir() -> PathBuf {
    // CARGO_MANIFEST_DIR is the path to this crate's Cargo.toml at compile time. Two levels up is
    // the workspace root; `target/lean_multisig_hints/` is the cache dir.
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join("target")
        .join("lean_multisig_hints")
}

fn cache_path(bytecode_hash: &[F; 8]) -> PathBuf {
    cache_dir().join(format!("{}.json", hash_to_hex(bytecode_hash)))
}

fn read_map(bytecode_hash: &[F; 8]) -> BTreeMap<String, CachedHints> {
    let path = cache_path(bytecode_hash);
    match std::fs::read_to_string(&path) {
        Ok(s) => serde_json::from_str(&s).unwrap_or_default(),
        Err(_) => BTreeMap::new(),
    }
}

fn write_map(bytecode_hash: &[F; 8], map: &BTreeMap<String, CachedHints>) -> std::io::Result<()> {
    let dir = cache_dir();
    std::fs::create_dir_all(&dir)?;
    let path = cache_path(bytecode_hash);
    let json = serde_json::to_string_pretty(map).expect("serialize CachedHints map");
    std::fs::write(&path, json)
}

/// Look up cached tight hints for the given (bytecode, workload). Returns `None` on cache miss
/// (including missing file or unparseable contents — treated as miss, not error).
pub fn load(bytecode_hash: &[F; 8], n_xmss: usize, n_recursions: usize) -> Option<ExecutionHints> {
    let map = read_map(bytecode_hash);
    map.get(&workload_key(n_xmss, n_recursions))
        .cloned()
        .map(ExecutionHints::from)
}

/// Persist the (bytecode, workload) → hints mapping so the next run can skip the heuristic +
/// retry. Failures are logged but never surfaced — the cache is a perf optimization, not a
/// correctness requirement.
pub fn save(bytecode_hash: &[F; 8], n_xmss: usize, n_recursions: usize, hints: &ExecutionHints) {
    let mut map = read_map(bytecode_hash);
    map.insert(workload_key(n_xmss, n_recursions), CachedHints::from(hints));
    if let Err(e) = write_map(bytecode_hash, &map) {
        tracing::warn!("failed to write ExecutionHints cache: {e}");
    }
}
