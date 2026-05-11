//! Random search for 8x8 *circulant* MDS matrices over the Goldilocks
//! field (p = 2^64 - 2^32 + 1) where most first-row entries come from a
//! small fixed set of "nice" constants.
//!
//! An 8x8 circulant matrix is parameterized by its first row
//! `(c0, c1, c2, c3, c4, c5, c6, c7)`; row `i` is row 0 rotated right by `i`:
//!
//!     M[i][j] = c[(j - i) mod 8]
//!
//! Constraints (per attempt):
//!   * `a` of the 8 first-row entries are arbitrary nonzero field elements ("big")
//!   * the remaining `8 - a` entries are sampled uniformly from `SMALL_VALUE_SPECS`
//!     (after dedup mod p)
//!   * every k x k minor of the matrix is nonzero (MDS), k = 1..=8
//!
//! `a` starts at `A` and is decremented by 1 each time an MDS matrix is found,
//! so each successive hit pins down a tighter solution. The search terminates
//! after a hit at a=0.
//!
//! Also: when `a == 0` and `SMALL_VALUE_SPECS` has few enough values that
//! `n_smalls^8` is tractable, the search switches to *exhaustive enumeration*
//! (every first row over the small set) instead of random sampling, so we
//! either prove no all-small circulant MDS exists or enumerate them all.
//!
//! Run with:
//!     cargo run --release --example mds_search_circulant

#![allow(clippy::needless_range_loop, clippy::too_many_lines)]

use std::io::Write;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Instant;

use goldilocks::Goldilocks;
use rand::{RngExt, SeedableRng, rngs::SmallRng};

// =====================================================================
// Tunable parameters
// =====================================================================

/// Maximum number of "big" (free) entries among the 8 first-row entries.
/// Also the starting value: each MDS find decrements the active count by 1.
const A: usize = 1;

/// Allowed values for "small" entries, as `(sign, k)` meaning `sign * 2^k mod p`.
/// Values that alias mod p are deduplicated at startup. Default: small powers
/// of two ±2^k for k ∈ {0, 1, 2, 3, 4, 5, 6, 32, 64}.
const SMALL_VALUE_SPECS: &[(i8, u32)] = &[(1, 0), (-1, 0), (1, 1), (-1, 1), (1, 2), (-1, 2), (1, 3)];

/// Threshold above which exhaustive enumeration at a=0 is skipped (fall back
/// to random sampling). `n_smalls^8 > this` => stay random.
const EXHAUSTIVE_LIMIT: u64 = 50_000_000;

/// Counter batch size: per-thread attempts before flushing to the shared atomic.
const COUNTER_BATCH: u64 = 1024;

/// Per-thread cap on random attempts at a single value of `a`. Prevents the
/// random pre-pass from spinning forever when a particular `a` has no solution.
const MAX_RANDOM_PER_THREAD: u64 = 200_000_000;

// =====================================================================
// Fixed
// =====================================================================

const N: usize = 8;
type F = Goldilocks;
const ZERO: F = Goldilocks::new(0);

/// `2^k mod p` via square-and-multiply.
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

fn embed_spec((sign, k): (i8, u32)) -> F {
    let v = pow2_mod_p(k);
    if sign < 0 { -v } else { v }
}

fn spec_str((sign, k): (i8, u32)) -> String {
    let s = if sign < 0 { "-" } else { "" };
    if k == 0 { format!("{s}1") } else { format!("{s}2^{k}") }
}

fn specs_list_str(specs: &[(i8, u32)]) -> String {
    specs.iter().map(|&s| spec_str(s)).collect::<Vec<_>>().join(", ")
}

// =====================================================================
// Subset enumeration (k-subsets of {0..N-1}).
// =====================================================================

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
// =====================================================================

#[inline]
fn is_singular(m: &[[F; N]; N], rows: &[u8], cols: &[u8], k: usize) -> bool {
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
    if k == 3 {
        let r0 = rows[0] as usize;
        let r1 = rows[1] as usize;
        let r2 = rows[2] as usize;
        let c0 = cols[0] as usize;
        let c1 = cols[1] as usize;
        let c2 = cols[2] as usize;
        let m00 = m[r0][c0];
        let m01 = m[r0][c1];
        let m02 = m[r0][c2];
        let m10 = m[r1][c0];
        let m11 = m[r1][c1];
        let m12 = m[r1][c2];
        let m20 = m[r2][c0];
        let m21 = m[r2][c1];
        let m22 = m[r2][c2];
        let det = m00 * (m11 * m22 - m12 * m21) - m01 * (m10 * m22 - m12 * m20) + m02 * (m10 * m21 - m11 * m20);
        return det == ZERO;
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

fn is_mds(m: &[[F; N]; N], subsets: &[Vec<[u8; N]>]) -> bool {
    for i in 0..N {
        for j in 0..N {
            if m[i][j] == ZERO {
                return false;
            }
        }
    }
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
// Build a circulant matrix from a first row.
//   M[i][j] = first_row[(j - i) mod N]
// =====================================================================

#[inline]
fn build_circulant(first_row: &[F; N]) -> [[F; N]; N] {
    let mut m = [[ZERO; N]; N];
    for i in 0..N {
        for j in 0..N {
            m[i][j] = first_row[(j + N - i) % N];
        }
    }
    m
}

// =====================================================================
// Canonicalize a circulant by rotation: circ(rot_r(c)) is a permutation
// of rows/cols of circ(c), so MDS is rotation-invariant. Pick the
// lexicographically smallest rotation as canonical form.
// =====================================================================

fn canon_rotation(specs: &[(i8, u32); N]) -> [(i8, u32); N] {
    let mut best = *specs;
    for r in 1..N {
        let mut rot = [(0i8, 0u32); N];
        for i in 0..N {
            rot[i] = specs[(i + r) % N];
        }
        if rot < best {
            best = rot;
        }
    }
    best
}

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd)]
struct Niceness {
    distinct: u32,
    sum_abs_k: u32,
    n_neg: u32,
    tiebreak: [(i8, u32); N],
}

fn score(specs: &[(i8, u32); N]) -> Niceness {
    let mut seen: Vec<(i8, u32)> = Vec::with_capacity(N);
    let mut sum_abs_k = 0u32;
    let mut n_neg = 0u32;
    for &sp in specs {
        if !seen.contains(&sp) {
            seen.push(sp);
        }
        sum_abs_k += sp.1;
        if sp.0 < 0 {
            n_neg += 1;
        }
    }
    Niceness {
        distinct: seen.len() as u32,
        sum_abs_k,
        n_neg,
        tiebreak: *specs,
    }
}

// =====================================================================
// Sample a random first row with `a` big entries (uniform nonzero) and
// `N - a` small entries from `smalls`. Returns the row and the big-position
// buffer (first `a` slots valid).
// =====================================================================

fn sample_first_row(rng: &mut SmallRng, smalls: &[F], a: usize) -> ([F; N], [u8; N]) {
    let mut chosen: u8 = 0; // 8-bit mask over positions
    let mut big_pos = [0u8; N];
    let mut placed = 0;
    while placed < a {
        let p = (rng.random::<u64>() & 7) as usize;
        let bit = 1u8 << p;
        if chosen & bit == 0 {
            chosen |= bit;
            big_pos[placed] = p as u8;
            placed += 1;
        }
    }
    let n_smalls = smalls.len() as u64;
    let mut row = [ZERO; N];
    for pos in 0..N {
        if chosen & (1u8 << pos) != 0 {
            let mut v: F = rng.random();
            while v == ZERO {
                v = rng.random();
            }
            row[pos] = v;
        } else {
            row[pos] = smalls[(rng.random::<u64>() % n_smalls) as usize];
        }
    }
    (row, big_pos)
}

// =====================================================================
// Pretty printing.
// =====================================================================

fn fmt_spec((s, k): (i8, u32)) -> String {
    let sign = if s < 0 { "-" } else { " " };
    if k == 0 {
        format!("{sign}1")
    } else {
        format!("{sign}2^{k}")
    }
}

fn classify_entry(v: F, smalls_values: &[F], smalls_specs: &[(i8, u32)]) -> Option<(i8, u32)> {
    for (i, &sv) in smalls_values.iter().enumerate() {
        if v == sv {
            return Some(smalls_specs[i]);
        }
    }
    None
}

fn print_hit(first_row: &[F; N], big_pos: &[u8], a: usize, smalls_values: &[F], smalls_specs: &[(i8, u32)]) {
    let m = build_circulant(first_row);
    let mut is_big = [false; N];
    for &p in &big_pos[..a] {
        is_big[p as usize] = true;
    }
    println!(
        "=== circulant MDS  (a={a} big entries; smalls = [{}]) ===",
        specs_list_str(smalls_specs)
    );
    print!("first row (spec/value) :");
    for i in 0..N {
        if is_big[i] {
            print!("  {:>20}*", first_row[i]);
        } else if let Some(sp) = classify_entry(first_row[i], smalls_values, smalls_specs) {
            print!("  {:>20}  ({})", first_row[i], fmt_spec(sp));
        } else {
            print!("  {:>20}", first_row[i]);
        }
    }
    println!();
    println!("matrix (rows; entries marked '*' are big):");
    for i in 0..N {
        print!("  [");
        for j in 0..N {
            let src = (j + N - i) % N;
            if is_big[src] {
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

// =====================================================================
// Main.
// =====================================================================

fn main() {
    let num_threads = std::thread::available_parallelism().unwrap().get();

    // Dedup small specs mod p.
    let mut smalls_values: Vec<F> = Vec::new();
    let mut smalls_specs: Vec<(i8, u32)> = Vec::new();
    for &sp in SMALL_VALUE_SPECS {
        let v = embed_spec(sp);
        if !smalls_values.contains(&v) {
            smalls_values.push(v);
            smalls_specs.push(sp);
        }
    }
    assert!(!smalls_values.is_empty(), "SMALL_VALUE_SPECS must be non-empty");
    assert!(smalls_values.iter().all(|f| *f != ZERO), "0 is not a valid small value");
    let smalls_values = Arc::new(smalls_values);
    let smalls_specs = Arc::new(smalls_specs);

    eprintln!(
        "Goldilocks 8x8 circulant MDS search: starting at a={A} big entries; smalls=[{}] ({} distinct); threads={num_threads}",
        specs_list_str(&smalls_specs),
        smalls_values.len()
    );

    let subsets: Vec<Vec<[u8; N]>> = (0..=N).map(|k| subsets_of_size(N, k)).collect();
    let total_minors: usize = (1..=N).map(|k| subsets[k].len() * subsets[k].len()).sum();
    eprintln!("Total k x k minors per matrix: {total_minors}");

    let subsets = Arc::new(subsets);
    let counter = Arc::new(AtomicU64::new(0));
    let hits = Arc::new(AtomicU64::new(0));
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
        let smalls_values = smalls_values.clone();
        let smalls_specs = smalls_specs.clone();
        handles.push(thread::spawn(move || {
            let seed = 0xBADC_0FFE_E0DD_F00Du64.wrapping_add((tid as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15));
            let mut rng = SmallRng::seed_from_u64(seed);
            let mut local_n: u64 = 0;
            let mut attempts_at_a: u64 = 0;
            let mut prev_a: usize = current_a.load(Ordering::Relaxed);
            loop {
                let a = current_a.load(Ordering::Relaxed);
                if a == usize::MAX {
                    counter.fetch_add(local_n, Ordering::Relaxed);
                    return;
                }
                if a != prev_a {
                    attempts_at_a = 0;
                    prev_a = a;
                }
                if attempts_at_a >= MAX_RANDOM_PER_THREAD {
                    // Give up on this `a` — but don't poison the search; other threads may
                    // still be lucky. Single thread early-out:
                    counter.fetch_add(local_n, Ordering::Relaxed);
                    return;
                }
                attempts_at_a += 1;
                let (row, big) = sample_first_row(&mut rng, &smalls_values, a);
                let m = build_circulant(&row);
                if is_mds(&m, &subsets) {
                    hits.fetch_add(1, Ordering::Relaxed);
                    let g = print_lock.lock().unwrap();
                    eprintln!();
                    println!("[thread {tid}]");
                    print_hit(&row, &big, a, &smalls_values, &smalls_specs);
                    let _ = std::io::stdout().flush();
                    let next = if a == 0 { usize::MAX } else { a - 1 };
                    let _ = current_a.compare_exchange(a, next, Ordering::Relaxed, Ordering::Relaxed);
                    drop(g);
                }
                local_n += 1;
                if local_n == COUNTER_BATCH {
                    let prev = counter.fetch_add(COUNTER_BATCH, Ordering::Relaxed);
                    local_n = 0;
                    if tid == 0 {
                        let total = prev + COUNTER_BATCH;
                        let dt = start.elapsed().as_secs_f64();
                        let mut err = std::io::stderr().lock();
                        let _ = write!(
                            err,
                            "\r[{:>7.1}s] a={} tried {:>11} ({:>6.2}M/s) hits {}    ",
                            dt,
                            current_a.load(Ordering::Relaxed),
                            total,
                            total as f64 / dt / 1e6,
                            hits.load(Ordering::Relaxed),
                        );
                        let _ = err.flush();
                    }
                }
            }
        }));
    }
    for h in handles {
        h.join().unwrap();
    }
    eprintln!();

    // -----------------------------------------------------------------
    // Bonus pass: if a=0 was hit and `n_smalls^N` is small enough,
    // enumerate every all-small first row to characterize the full set.
    // -----------------------------------------------------------------
    let n_smalls = smalls_values.len() as u64;
    let total_all_small: u64 = n_smalls.pow(N as u32);
    if total_all_small <= EXHAUSTIVE_LIMIT {
        eprintln!(
            "\nExhaustive a=0 enumeration: {} candidates over {} distinct small values.",
            total_all_small,
            smalls_values.len()
        );
        let exhaustive_start = Instant::now();
        let progress = AtomicU64::new(0);
        let bonus_hits = Mutex::new(Vec::<[(i8, u32); N]>::new());
        let chunk = total_all_small.div_ceil(num_threads as u64);

        thread::scope(|s| {
            for tid in 0..num_threads {
                let lo = (tid as u64) * chunk;
                let hi = (((tid as u64) + 1) * chunk).min(total_all_small);
                if lo >= hi {
                    continue;
                }
                let smalls_values = smalls_values.clone();
                let smalls_specs = smalls_specs.clone();
                let subsets = subsets.clone();
                let bonus_hits = &bonus_hits;
                let progress = &progress;
                s.spawn(move || {
                    let mut row = [ZERO; N];
                    let mut specs = [(0i8, 0u32); N];
                    let mut local = 0u64;
                    for idx in lo..hi {
                        let mut x = idx;
                        for r in 0..N {
                            let s_idx = (x as usize) % smalls_values.len();
                            row[r] = smalls_values[s_idx];
                            specs[r] = smalls_specs[s_idx];
                            x /= smalls_values.len() as u64;
                        }
                        let m = build_circulant(&row);
                        if is_mds(&m, &subsets) {
                            bonus_hits.lock().unwrap().push(specs);
                        }
                        local += 1;
                        if local.is_multiple_of(131_072) {
                            let p = progress.fetch_add(131_072, Ordering::Relaxed) + 131_072;
                            if tid == 0 {
                                let dt = exhaustive_start.elapsed().as_secs_f64();
                                let mut err = std::io::stderr().lock();
                                let _ = write!(
                                    err,
                                    "\r[exhaustive {:>5.1}s] {:>11}/{} ({:>6.2}M/s)   ",
                                    dt,
                                    p,
                                    total_all_small,
                                    p as f64 / dt / 1e6,
                                );
                                let _ = err.flush();
                            }
                        }
                    }
                    progress.fetch_add(local % 131_072, Ordering::Relaxed);
                });
            }
        });
        eprintln!();
        let bonus = bonus_hits.into_inner().unwrap();
        eprintln!(
            "Exhaustive done: {} all-small circulant MDS matrices found.",
            bonus.len()
        );

        let mut canonical: Vec<[(i8, u32); N]> = bonus.iter().map(canon_rotation).collect();
        canonical.sort_unstable();
        canonical.dedup();
        eprintln!(
            "After canonicalization by rotation: {} distinct circulant classes.",
            canonical.len()
        );

        let mut ranked: Vec<([(i8, u32); N], Niceness)> = canonical.iter().map(|r| (*r, score(r))).collect();
        ranked.sort_by(|a, b| a.1.cmp(&b.1));

        let top = ranked.len().min(10);
        println!("\n===== Top {top} nicest circulant MDS classes (by #distinct, sum|k|, #neg) =====\n");
        for (i, (specs, sc)) in ranked.iter().take(top).enumerate() {
            let mut row = [ZERO; N];
            for j in 0..N {
                row[j] = embed_spec(specs[j]);
            }
            println!(
                "#{}  distinct={} sum|k|={} n_neg={}",
                i + 1,
                sc.distinct,
                sc.sum_abs_k,
                sc.n_neg
            );
            print_hit(&row, &[0u8; N], 0, &smalls_values, &smalls_specs);
        }
    }
}
