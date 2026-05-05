//! Standalone reproducer for the bug `flush_rayon` exists to prevent.
//!
//! Run:
//!
//!     cargo run --release --example rayon_arena_mre -p zk-alloc
//!
//! Expected output: a "CORRUPTION" line showing that a `JobRef` from rayon's
//! global `crossbeam_deque::Injector` overwrote bytes in our canary buffer.
//!
//! How it works:
//!   - `Arena` is a tiny bump-pointer allocator that owns one slab. `begin_phase`
//!     resets the bump pointer; `dealloc` is a no-op for arena pointers. Only the
//!     main thread routes through it; every other thread falls back to System.
//!   - Phase 1 issues many `rayon::join`s from the main thread. Each one calls
//!     `Injector::push`, and the `Injector`'s linked list eventually allocates a
//!     fresh block while `ARENA_ACTIVE` is true — that block lives inside the slab.
//!   - `end_phase` + `begin_phase` resets the bump pointer. The Injector still
//!     holds a pointer into the (now reusable) slab memory.
//!   - Phase 2 allocates a canary buffer at the start of the slab, snapshots it,
//!     then issues one more `rayon::join`. That push writes a `JobRef` straight
//!     through the dangling block pointer into the canary.

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

const SLAB_SIZE: usize = 1 << 22; // 4 MiB

struct Arena;

static ACTIVE: AtomicBool = AtomicBool::new(false);
static SLAB_BASE: AtomicUsize = AtomicUsize::new(0);

thread_local! {
    static IS_MAIN: Cell<bool> = const { Cell::new(false) };
    static BUMP: Cell<usize> = const { Cell::new(0) };
}

unsafe impl GlobalAlloc for Arena {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        if ACTIVE.load(Ordering::Relaxed) && IS_MAIN.with(Cell::get) {
            let cur = BUMP.with(Cell::get);
            let aligned = (cur + layout.align() - 1) & !(layout.align() - 1);
            let next = aligned + layout.size();
            let end = SLAB_BASE.load(Ordering::Relaxed) + SLAB_SIZE;
            if next <= end {
                BUMP.with(|c| c.set(next));
                return aligned as *mut u8;
            }
        }
        unsafe { System.alloc(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        let base = SLAB_BASE.load(Ordering::Relaxed);
        let addr = ptr as usize;
        if base != 0 && addr >= base && addr < base + SLAB_SIZE {
            return; // arena: free is a no-op
        }
        unsafe { System.dealloc(ptr, layout) };
    }
}

#[global_allocator]
static A: Arena = Arena;

fn init() {
    IS_MAIN.with(|c| c.set(true));
    let layout = Layout::from_size_align(SLAB_SIZE, 4096).unwrap();
    let ptr = unsafe { System.alloc(layout) };
    assert!(!ptr.is_null());
    SLAB_BASE.store(ptr as usize, Ordering::Release);
}

fn begin_phase() {
    BUMP.with(|c| c.set(SLAB_BASE.load(Ordering::Relaxed)));
    ACTIVE.store(true, Ordering::Release);
}

fn end_phase() {
    ACTIVE.store(false, Ordering::Release);
}

fn main() {
    init();

    // Warm rayon up while the arena is off, so its initial Injector block lands
    // in System rather than in the slab.
    rayon::join(|| {}, || {});

    // Phase 1: enough top-level joins to rotate the Injector tail past its initial
    // block. The replacement block(s) get allocated by `Injector::push` while
    // ARENA_ACTIVE is true, so they live inside the slab.
    begin_phase();
    for _ in 0..200 {
        rayon::join(|| {}, || {});
    }
    end_phase();

    // Phase 2: drop a canary buffer at the start of the slab and snapshot it. The
    // Injector still holds a pointer into the (now reset) slab; the next push
    // writes a `JobRef` through that pointer.
    begin_phase();
    let canary = vec![0xAB_u8; 8192];
    let original = canary.clone();
    rayon::join(|| {}, || {});
    end_phase();

    let diffs: Vec<_> = canary
        .iter()
        .zip(&original)
        .enumerate()
        .filter(|(_, (now, was))| now != was)
        .take(8)
        .collect();

    if diffs.is_empty() {
        println!("no corruption — bug NOT reproduced (try increasing the loop count)");
    } else {
        println!("CORRUPTION: rayon's Injector::push wrote into our canary buffer");
        for (i, (now, was)) in diffs {
            println!("  canary[{i:>5}]: 0x{was:02x} -> 0x{now:02x}");
        }
    }
}
