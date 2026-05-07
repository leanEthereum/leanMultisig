//! Random search for 8x8 MDS matrices over the Goldilocks field
//! (p = 2^64 - 2^32 + 1) where most entries are small.
//!
//! Constraints:
//!   * exactly `A` of the 64 entries are arbitrary field elements ("big")
//!   * the remaining `64 - A` entries lie in {1, ..., B-1}        ("small")
//!   * every k x k minor of the matrix is nonzero (MDS), k = 1..=8
//!
//! The search picks the A "big" positions uniformly at random for each
//! attempt (free placement). Multi-threaded via `std::thread`.
//!
//! Run with:
//!     cargo run --release --example mds_search
//!
//! Tune A, B, NUM_THREADS at the top of the file. Field arithmetic is
//! reused from `crates/backend/goldilocks` (the in-tree `mt-goldilocks`
//! crate).

use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::thread;
use std::time::Instant;

use goldilocks::Goldilocks;
use rand::{RngExt, SeedableRng, rngs::StdRng};

// =====================================================================
// Tunable parameters
// =====================================================================

/// Number of "big" (free) entries among the 64 matrix entries.
const A: usize = 8;

/// Small entries are sampled uniformly from {1, ..., B-1}.
const B: u64 = 8;

const NUM_THREADS: usize = 8;

// =====================================================================
// Fixed
// =====================================================================

const N: usize = 8;

type F = Goldilocks;

/// Canonical zero. `Goldilocks::PartialEq` compares canonicalized values,
/// so `x == ZERO` correctly tests "is this the zero element".
const ZERO: F = Goldilocks::new(0);

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
// Random matrix generator subject to (A big, 64-A small) constraint.
// =====================================================================

fn sample(rng: &mut StdRng) -> ([[F; N]; N], [u8; A]) {
    let mut chosen = [false; N * N];
    let mut big_pos = [0u8; A];
    let mut placed = 0;
    while placed < A {
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
            // small: in {1, ..., B-1}
            let v = rng.random_range(1..B);
            m[i][j] = Goldilocks::new(v);
        }
    }
    (m, big_pos)
}

fn print_hit(m: &[[F; N]; N], big_pos: &[u8; A]) {
    let mut is_big = [[false; N]; N];
    for &p in big_pos {
        is_big[p as usize / N][p as usize % N] = true;
    }
    println!("=== MDS matrix found (A={}, B={}) ===", A, B);
    let mut bp: Vec<(usize, usize)> = big_pos
        .iter()
        .map(|&p| (p as usize / N, p as usize % N))
        .collect();
    bp.sort();
    println!("Big positions (row,col): {:?}", bp);
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
    eprintln!(
        "Goldilocks 8x8 MDS search: A={} big entries, small in {{1..{}}}, threads={}",
        A,
        B - 1,
        NUM_THREADS
    );

    let subsets: Vec<Vec<[u8; N]>> = (0..=N).map(|k| subsets_of_size(N, k)).collect();
    let total_minors: usize = (1..=N).map(|k| subsets[k].len() * subsets[k].len()).sum();
    eprintln!("Total k x k minors per matrix: {total_minors}");

    let subsets = Arc::new(subsets);
    let counter = Arc::new(AtomicU64::new(0));
    let hits = Arc::new(AtomicU64::new(0));
    let start = Instant::now();

    let mut handles = Vec::with_capacity(NUM_THREADS);
    for tid in 0..NUM_THREADS {
        let subsets = subsets.clone();
        let counter = counter.clone();
        let hits = hits.clone();
        handles.push(thread::spawn(move || {
            let mut rng = StdRng::seed_from_u64(0xDEAD_BEEF_1234_5678 ^ tid as u64);
            loop {
                let (m, big) = sample(&mut rng);
                if is_mds(&m, &subsets) {
                    hits.fetch_add(1, Ordering::Relaxed);
                    println!("\n[thread {tid}]");
                    print_hit(&m, &big);
                }
                let n = counter.fetch_add(1, Ordering::Relaxed) + 1;
                if tid == 0 && n % 1024 == 0 {
                    let dt = start.elapsed().as_secs_f64();
                    eprintln!(
                        "[{:>7.1}s] tried {:>10} ({:>8.1}/s), hits {}",
                        dt,
                        n,
                        n as f64 / dt,
                        hits.load(Ordering::Relaxed)
                    );
                }
            }
        }));
    }
    for h in handles {
        h.join().unwrap();
    }
}
