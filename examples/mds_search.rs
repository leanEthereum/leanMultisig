//! Random search for 8x8 MDS matrices over the Goldilocks field
//! (p = 2^64 - 2^32 + 1) where most entries come from a small fixed set.
//!
//! Constraints (per attempt):
//!   * `a` of the 64 entries are arbitrary nonzero field elements ("big")
//!   * the remaining `64 - a` entries are sampled uniformly from
//!     `SMALL_VALUE_SPECS` (after dedup mod p)
//!   * every k x k minor of the matrix is nonzero (MDS), k = 1..=8
//!
//! `a` starts at the cap `A` and is decremented by 1 each time an MDS
//! matrix is found, so each successive hit pins down a tighter solution
//! (more small entries). The search terminates after a hit at a=0.
//! The big-entry positions themselves are chosen uniformly at random
//! per attempt (free placement). Multi-threaded; uses all cores.
//!
//! Run with:
//!     cargo run --release --example mds_search
//!
//! Tune `A` and `SMALL_VALUE_SPECS` at the top of the file. Field
//! arithmetic is reused from `crates/backend/goldilocks` (the in-tree
//! `mt-goldilocks` crate).

#![allow(clippy::needless_range_loop)]

use std::io::Write;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Instant;

use goldilocks::Goldilocks;
use rand::{RngExt, SeedableRng, rngs::StdRng};

// =====================================================================
// Tunable parameters
// =====================================================================

/// Maximum number of "big" (free) entries among the 64 matrix entries.
/// Also the starting value: each MDS find decrements the active count by 1.
const A: usize = 32;

/// Allowed values for "small" entries, given as `(sign, k)` meaning
/// `sign * 2^k mod p`. The full set is fixed throughout the search.
/// Values that alias mod p are deduplicated at startup.
///
/// Default: `{±2^k : k ∈ {0, 32, 64, 96, 128, 160}}`. Note that
/// `2^96 ≡ -1`, `2^128 ≡ -2^32`, `2^160 ≡ -(2^64) (mod p)`, so the last
/// six specs alias to existing values and are dropped.
const SMALL_VALUE_SPECS: &[(i8, u32)] = &[
    (1, 0),
    (-1, 0),
    (1, 32),
    (-1, 32),
    (1, 64),
    (-1, 64),
    (1, 96),
    (-1, 96),
    (1, 128),
    (-1, 128),
    (1, 160),
    (-1, 160),
];

// =====================================================================
// Fixed
// =====================================================================

const N: usize = 8;

type F = Goldilocks;

/// Canonical zero. `Goldilocks::PartialEq` compares canonicalized values,
/// so `x == ZERO` correctly tests "is this the zero element".
const ZERO: F = Goldilocks::new(0);

/// `2^k mod p` via square-and-multiply. Called once per spec at startup.
fn pow2_mod_p(mut k: u32) -> F {
    let mut base = Goldilocks::new(2);
    let mut acc = Goldilocks::new(1);
    while k > 0 {
        if k & 1 == 1 {
            acc *= base;
        }
        base *= base;
        k >>= 1;
    }
    acc
}

/// Embed a `(sign, k)` spec as `sign * 2^k` in Goldilocks.
fn embed_spec((sign, k): (i8, u32)) -> F {
    let v = pow2_mod_p(k);
    if sign < 0 { -v } else { v }
}

fn spec_str((sign, k): (i8, u32)) -> String {
    if sign < 0 { format!("-2^{k}") } else { format!("2^{k}") }
}

fn specs_str(specs: &[(i8, u32)]) -> String {
    specs.iter().map(|&s| spec_str(s)).collect::<Vec<_>>().join(", ")
}

// =====================================================================
// Subset enumeration
// =====================================================================

/// All k-subsets of {0, ..., n-1}, each stored as a `[u8; N]` with the
/// first k entries the (sorted) members and the rest unused.
fn subsets_of_size(n: usize, k: usize) -> Vec<[u8; N]> {
    fn rec(start: usize, n: usize, k: usize, cur: &mut Vec<u8>, out: &mut Vec<[u8; N]>) {
        if cur.len() == k {
            let mut arr = [0u8; N];
            for (i, &v) in cur.iter().enumerate() {
                arr[i] = v;
            }
            out.push(arr);
            return;
        }
        for i in start..n {
            cur.push(i as u8);
            rec(i + 1, n, k, cur, out);
            cur.pop();
        }
    }
    let mut out = Vec::new();
    rec(0, n, k, &mut Vec::with_capacity(k), &mut out);
    out
}

// =====================================================================
// Singularity check via fraction-free Gaussian elimination.
// We only care whether the determinant is zero, so we do
//     row_r <- pivot * row_r - factor * row_pivot
// which scales the determinant by `pivot` (nonzero), preserving zeroness.
// =====================================================================

#[inline]
fn is_singular(m: &[[F; N]; N], rows: &[u8], cols: &[u8], k: usize) -> bool {
    // Hardcode small cases for speed.
    if k == 1 {
        return m[rows[0] as usize][cols[0] as usize] == ZERO;
    }
    if k == 2 {
        let a = m[rows[0] as usize][cols[0] as usize];
        let b = m[rows[0] as usize][cols[1] as usize];
        let c = m[rows[1] as usize][cols[0] as usize];
        let d = m[rows[1] as usize][cols[1] as usize];
        return a * d - b * c == ZERO;
    }

    let mut a = [[ZERO; N]; N];
    for i in 0..k {
        let r = rows[i] as usize;
        for j in 0..k {
            a[i][j] = m[r][cols[j] as usize];
        }
    }
    for i in 0..k {
        let mut piv = i;
        while piv < k && a[piv][i] == ZERO {
            piv += 1;
        }
        if piv == k {
            return true;
        }
        if piv != i {
            a.swap(i, piv);
        }
        let p = a[i][i];
        for r in (i + 1)..k {
            if a[r][i] == ZERO {
                continue;
            }
            let f = a[r][i];
            for c in i..k {
                a[r][c] = p * a[r][c] - f * a[i][c];
            }
        }
    }
    false
}

// =====================================================================
// MDS check: every minor of every size in 1..=N must be nonzero.
// Fail-fast on the first vanishing minor.
// =====================================================================

fn is_mds(m: &[[F; N]; N], subsets: &[Vec<[u8; N]>]) -> bool {
    // Size 1: any zero entry kills MDS immediately.
    for i in 0..N {
        for j in 0..N {
            if m[i][j] == ZERO {
                return false;
            }
        }
    }
    // Sizes 2..=N.
    for k in 2..=N {
        for rs in &subsets[k] {
            for cs in &subsets[k] {
                if is_singular(m, &rs[..k], &cs[..k], k) {
                    return false;
                }
            }
        }
    }
    true
}

// =====================================================================
// Random matrix generator: `a` big entries placed uniformly at random
// (sampled uniformly nonzero in F), the remaining `64 - a` entries sampled
// uniformly from `smalls`. The returned `[u8; A]` is the big-position
// buffer; only the first `a` slots are valid.
// =====================================================================

fn sample(rng: &mut StdRng, smalls: &[F], a: usize) -> ([[F; N]; N], [u8; A]) {
    let mut chosen = [false; N * N];
    let mut big_pos = [0u8; A];
    let mut placed = 0;
    while placed < a {
        let p = rng.random_range(0..(N * N));
        if !chosen[p] {
            chosen[p] = true;
            big_pos[placed] = p as u8;
            placed += 1;
        }
    }

    let mut m = [[ZERO; N]; N];
    for p in 0..N * N {
        let i = p / N;
        let j = p % N;
        if chosen[p] {
            // big: nonzero element of F_p (zero would fail the 1x1 check anyway)
            let mut v: F = rng.random();
            while v == ZERO {
                v = rng.random();
            }
            m[i][j] = v;
        } else {
            // small: pick uniformly from the active small-value set
            m[i][j] = smalls[rng.random_range(0..smalls.len())];
        }
    }
    (m, big_pos)
}

fn print_hit(m: &[[F; N]; N], big_pos: &[u8], smalls: &[(i8, u32)]) {
    let mut is_big = [[false; N]; N];
    for &p in big_pos {
        is_big[p as usize / N][p as usize % N] = true;
    }
    println!(
        "=== MDS matrix found (a={}, smalls=[{}]) ===",
        big_pos.len(),
        specs_str(smalls)
    );
    let mut bp: Vec<(usize, usize)> = big_pos.iter().map(|&p| (p as usize / N, p as usize % N)).collect();
    bp.sort_unstable();
    println!("Big positions (row,col): {bp:?}");
    println!("Matrix (entries marked '*' are big):");
    for i in 0..N {
        print!("[");
        for j in 0..N {
            if is_big[i][j] {
                print!(" {:>20}*", m[i][j]);
            } else {
                print!(" {:>20} ", m[i][j]);
            }
            if j + 1 < N {
                print!(",");
            }
        }
        println!(" ]");
    }
    println!();
}

fn main() {
    let num_threads = std::thread::available_parallelism().unwrap().get();

    // Embed each spec, deduplicating values that alias mod p (e.g. 2^96 ≡ -1).
    let mut all_smalls: Vec<F> = Vec::new();
    let mut all_smalls_specs: Vec<(i8, u32)> = Vec::new();
    for &spec in SMALL_VALUE_SPECS {
        let v = embed_spec(spec);
        if !all_smalls.contains(&v) {
            all_smalls.push(v);
            all_smalls_specs.push(spec);
        }
    }
    assert!(!all_smalls.is_empty(), "SMALL_VALUE_SPECS must be non-empty");
    assert!(all_smalls.iter().all(|f| *f != ZERO), "0 is not a valid small value");
    let all_smalls = Arc::new(all_smalls);
    let all_smalls_specs = Arc::new(all_smalls_specs);

    eprintln!(
        "Goldilocks 8x8 MDS search: starting at a={A} big entries, small set [{}] ({} distinct), threads={num_threads}",
        specs_str(&all_smalls_specs),
        all_smalls.len()
    );

    let subsets: Vec<Vec<[u8; N]>> = (0..=N).map(|k| subsets_of_size(N, k)).collect();
    let total_minors: usize = (1..=N).map(|k| subsets[k].len() * subsets[k].len()).sum();
    eprintln!("Total k x k minors per matrix: {total_minors}");

    let subsets = Arc::new(subsets);
    let counter = Arc::new(AtomicU64::new(0));
    let hits = Arc::new(AtomicU64::new(0));
    // Sentinel `usize::MAX` means: a hit was found at a=0, so the search is done.
    let current_a = Arc::new(AtomicUsize::new(A));
    let print_lock = Arc::new(Mutex::new(()));
    let start = Instant::now();

    let mut handles = Vec::with_capacity(num_threads);
    for tid in 0..num_threads {
        let subsets = subsets.clone();
        let counter = counter.clone();
        let hits = hits.clone();
        let current_a = current_a.clone();
        let print_lock = print_lock.clone();
        let all_smalls = all_smalls.clone();
        let all_smalls_specs = all_smalls_specs.clone();
        handles.push(thread::spawn(move || {
            let mut rng = StdRng::seed_from_u64(0xDEAD_BEEF_1234_5678 ^ tid as u64);
            loop {
                let a = current_a.load(Ordering::Relaxed);
                if a == usize::MAX {
                    return;
                }
                let (m, big) = sample(&mut rng, &all_smalls, a);
                if is_mds(&m, &subsets) {
                    hits.fetch_add(1, Ordering::Relaxed);
                    let g = print_lock.lock().unwrap();
                    // Drop the in-place progress line and emit the match below it.
                    eprintln!();
                    println!("[thread {tid}]");
                    print_hit(&m, &big[..a], &all_smalls_specs);
                    let _ = std::io::stdout().flush();
                    // First finder at this `a` decrements; later finders at the same `a` are kept as bonus prints.
                    let next = if a == 0 { usize::MAX } else { a - 1 };
                    let _ = current_a.compare_exchange(a, next, Ordering::Relaxed, Ordering::Relaxed);
                    drop(g);
                }
                let n = counter.fetch_add(1, Ordering::Relaxed) + 1;
                if tid == 0 && n.is_multiple_of(1024) {
                    let dt = start.elapsed().as_secs_f64();
                    let mut err = std::io::stderr().lock();
                    let _ = write!(
                        err,
                        "\r[{:>7.1}s] a={} tried {:>11} ({:>6.2}M/s) hits {}    ",
                        dt,
                        current_a.load(Ordering::Relaxed),
                        n,
                        n as f64 / dt / 1e6,
                        hits.load(Ordering::Relaxed),
                    );
                    let _ = err.flush();
                }
            }
        }));
    }
    for h in handles {
        h.join().unwrap();
    }
    eprintln!();
}
