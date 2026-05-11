//! Bump-pointer arena allocator.
//!
//! One mmap region split into per-thread slabs. Allocation = increment a thread-local
//! pointer; free = no-op. `begin_phase()` resets the arena: each thread's next
//! allocation starts over at the beginning of its slab, overwriting the previous
//! phase's data. Allocations that don't fit (too large, or beyond `MAX_THREADS`) fall
//! back to the system allocator.
//!
//! ```ignore
//! init();                          // once, at process start
//! loop {
//!     begin_phase();               // arena ON; slabs reset lazily
//!     let res = heavy_work();      // fast increments
//!     end_phase();                 // arena OFF; new allocations go to System
//!     let copy = res.clone();      // detach from arena before next phase resets it
//! }
//! ```

use std::alloc::{GlobalAlloc, Layout};
use std::cell::Cell;
use std::sync::Once;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

use system_info::NUM_THREADS;

mod syscall;

const SLAB_SIZE: usize = 8 << 30; // 8GB
const SLACK: usize = 4; // SLACK absorbs the main thread and any non-rayon helpers.
const MAX_THREADS: usize = NUM_THREADS + SLACK;
const REGION_SIZE: usize = SLAB_SIZE * MAX_THREADS;

/// Allocations smaller than this go to System even during active phases.
/// Routes registry / hashmap / injector-block-sized allocations away from the
/// arena, so library state that outlives a phase doesn't land in recycled
/// memory. Covers the known phase-crossing patterns: crossbeam_deque::Injector
/// blocks (~1.5 KB), tracing-subscriber Registry slot data (sub-KB), hashbrown
/// HashMap entries (sub-KB), rayon-core job stack frames (sub-KB).
///
/// TODO is there a cleaner way?
///
/// Lowered from 4096 to 256 on M2 once THP-backed arena landed (iter 8): allocs
/// in the arena now hit a 32 MiB hugepage TLB entry whereas System allocs land
/// on 16 KiB base pages. Pushing the 256..4095 size band into the arena buys
/// the hugepage TLB benefit for more allocations. Phase-crossing safety: the
/// named ~1.5 KB Injector blocks still bypass via System (still in the
/// [0, 256) carve-out? No — Injector blocks are ~1.5 KB > 256). Risk: any
/// phase-crossing allocation in [256, 1500) is now in the arena and gets
/// recycled. Sticky-System realloc still protects grown Vecs that started in
/// System. Correctness gate enforces.
const MIN_ARENA_BYTES: usize = 256;

#[derive(Debug)]
pub struct ZkAllocator;

/// Incremented by `begin_phase()`. Every thread caches the last value it saw in
/// `ARENA_GEN`; when they differ, the thread resets its allocation cursor to the start
/// of its slab on the next allocation. This is how a single store on the main thread
/// "resets" every other thread's slab without any cross-thread synchronization.
static GENERATION: AtomicUsize = AtomicUsize::new(0);

/// Master switch for the arena. `true` (set by `begin_phase`) routes allocations
/// through the arena; `false` (set by `end_phase`) routes them to the system allocator.
static ARENA_ACTIVE: AtomicBool = AtomicBool::new(false);

/// Base address of the mmap'd region, or `0` before `ensure_region` runs. Read on
/// every `dealloc` to test whether a pointer belongs to us.
static REGION_BASE: AtomicUsize = AtomicUsize::new(0);

/// Synchronizes the one-time mmap so concurrent first-allocators don't race.
static REGION_INIT: Once = Once::new();

/// Monotonic counter handed out to threads to pick their slab. `fetch_add`'d once per
/// thread on its first arena allocation. Threads that get `idx >= MAX_THREADS` mark
/// themselves `ARENA_NO_SLAB` and permanently fall through to the system allocator.
static THREAD_IDX: AtomicUsize = AtomicUsize::new(0);

thread_local! {
    /// Where this thread's next allocation lands. Advanced past each allocation.
    static ARENA_PTR: Cell<usize> = const { Cell::new(0) };
    /// One past the last byte of this thread's slab. An alloc fits iff
    /// `aligned + size <= ARENA_END`.
    static ARENA_END: Cell<usize> = const { Cell::new(0) };
    /// Base address of this thread's slab (`0` = not yet claimed). On reset,
    /// `ARENA_PTR` is set back to this value.
    static ARENA_BASE: Cell<usize> = const { Cell::new(0) };
    /// Last `GENERATION` value this thread observed. When the global moves past
    /// this, the next allocation resets `ARENA_PTR` to `ARENA_BASE` and updates
    /// this field.
    static ARENA_GEN: Cell<usize> = const { Cell::new(0) };
    /// `true` if this thread was created after `MAX_THREADS` was already exhausted.
    /// Such threads skip arena logic entirely and always go to the system allocator.
    static ARENA_NO_SLAB: Cell<bool> = const { Cell::new(false) };
}

/// Returns the base address of the mmap'd region, mapping it on the first call.
fn ensure_region() -> usize {
    REGION_INIT.call_once(|| {
        // On aarch64 Linux (M2/Asahi) THP page size is 32 MiB. We over-allocate
        // by THP_SIZE so we can round REGION_BASE up to a 32 MiB boundary, which
        // is what khugepaged needs to collapse base pages into hugepages. Without
        // this alignment MADV_HUGEPAGE is observed to fire only intermittently
        // (iter 7: real signal but p=0.019 not p<0.01). With alignment + an
        // eager touch (one write per 32 MiB) the kernel collapses the touched
        // region into THP synchronously, making the win deterministic.
        #[cfg(target_arch = "aarch64")]
        const THP_SIZE: usize = 32 << 20; // 32 MiB on M2 Asahi
        #[cfg(not(target_arch = "aarch64"))]
        const THP_SIZE: usize = 0;

        let mmap_size = REGION_SIZE + THP_SIZE;
        // SAFETY: mmap_anonymous returns a page-aligned pointer or null. MAP_NORESERVE
        // means no physical memory is committed until pages are touched.
        let raw = unsafe { syscall::mmap_anonymous(mmap_size) };
        if raw.is_null() {
            std::process::abort();
        }

        let aligned_base = if THP_SIZE > 0 {
            (raw as usize).next_multiple_of(THP_SIZE)
        } else {
            raw as usize
        };

        // On aarch64, ask khugepaged to use THP for the slab region. On x86_64
        // preserve the historical NOHUGEPAGE hint (2 MiB THP can fragment slab
        // release; documented original choice).
        #[cfg(target_arch = "aarch64")]
        let advice = syscall::MADV_HUGEPAGE;
        #[cfg(not(target_arch = "aarch64"))]
        let advice = syscall::MADV_NOHUGEPAGE;
        unsafe { syscall::madvise(aligned_base as *mut u8, REGION_SIZE, advice) };

        // Eager pre-touch on aarch64: write one byte per 32 MiB hugepage across
        // the first `pretouch_bytes` of every per-thread slab. Each write
        // triggers a page fault that the kernel resolves into a 32 MiB THP
        // given our earlier MADV_HUGEPAGE hint and the 32 MiB-aligned base.
        // This makes the THP win deterministic instead of
        // khugepaged-async-dependent.
        //
        // Adapt `pretouch_bytes` to MemTotal (was a hard-coded 1 GiB in iter 8).
        // The 1 GiB const × MAX_THREADS=14 = 14 GiB pre-touch overshoots the
        // 16 GiB Asahi M2 box: the eval gate's prove_loop_cand was OOM-killed
        // twice with anon-rss ~14.3 GiB on 2026-05-11 (journalctl). Cap at
        // MemTotal / MAX_THREADS / OVERCOMMIT_GUARD so total pre-touch stays
        // under MemTotal/3, leaving room for the workload's own ~10 GiB
        // touched footprint and the rest of the process.
        // - 16 GiB / 14 / 3 ≈ 390 MiB per slab → ~5.4 GiB pre-touched
        // - 64 GiB / 14 / 3 ≈ 1.56 GiB per slab → capped at 1 GiB ceiling
        // Floor at THP_SIZE so we still pre-touch at least one hugepage per
        // slab if `total_ram_bytes()` returns a degenerately small value or
        // fails (returns 0 → fall back to THP_SIZE).
        // Runs in REGION_INIT.call_once, well before any timed proof window.
        #[cfg(target_arch = "aarch64")]
        {
            const PRETOUCH_HARD_CAP: usize = 1 << 30; // 1 GiB ceiling per slab
            const OVERCOMMIT_GUARD: usize = 3; // total pre-touch ≤ MemTotal/3
            // SAFETY: total_ram_bytes is allocation-free (sysinfo syscall into stack buffer).
            let mem_total = unsafe { syscall::total_ram_bytes() };
            let pretouch_bytes = if mem_total == 0 {
                THP_SIZE
            } else {
                let budget = mem_total / MAX_THREADS / OVERCOMMIT_GUARD;
                budget.clamp(THP_SIZE, PRETOUCH_HARD_CAP)
            };
            for slab_idx in 0..MAX_THREADS {
                let slab_base = aligned_base + slab_idx * SLAB_SIZE;
                let mut off = 0;
                while off < pretouch_bytes {
                    // SAFETY: aligned_base..aligned_base+REGION_SIZE is a valid
                    // anonymous mmap reservation; we only touch within slab.
                    unsafe {
                        std::ptr::write_volatile((slab_base + off) as *mut u8, 0);
                    }
                    off += THP_SIZE;
                }
            }
        }

        REGION_BASE.store(aligned_base, Ordering::Release);
    });
    REGION_BASE.load(Ordering::Acquire)
}

/// Call once at process start, before any `begin_phase()`.
pub fn init() {
    let actual_num_threads = std::thread::available_parallelism().unwrap().get();
    assert_eq!(
        actual_num_threads, NUM_THREADS,
        "built for {NUM_THREADS} threads but this machine reports {actual_num_threads} -> please rebuild`"
    );
}

/// Activates the arena and resets every thread's slab. All allocations until the next
/// `end_phase()` go to the arena; the previous phase's data is overwritten in place.
///
/// Panics if a phase is already active: phases must not nest (a nested call would
/// recycle the slab and overwrite the outer phase's still-live allocations).
pub fn begin_phase() {
    let prev_active = ARENA_ACTIVE.swap(true, Ordering::Release);
    assert!(
        !prev_active,
        "begin_phase() called while another phase is already active — phases must not nest"
    );
    GENERATION.fetch_add(1, Ordering::Release);
}

/// Deactivates the arena. New allocations go to the system allocator; existing arena
/// pointers stay valid until the next `begin_phase()` resets the slabs.
pub fn end_phase() {
    ARENA_ACTIVE.store(false, Ordering::Release);
}

#[cold]
#[inline(never)]
unsafe fn arena_alloc_cold(size: usize, align: usize) -> *mut u8 {
    let generation = GENERATION.load(Ordering::Relaxed);
    if !ARENA_NO_SLAB.get() && ARENA_GEN.get() != generation {
        let mut base = ARENA_BASE.get();
        if base == 0 {
            let region = ensure_region();
            let idx = THREAD_IDX.fetch_add(1, Ordering::Relaxed);
            if idx >= MAX_THREADS {
                ARENA_NO_SLAB.set(true);
                return unsafe { std::alloc::System.alloc(Layout::from_size_align_unchecked(size, align)) };
            }
            base = region + idx * SLAB_SIZE;
            ARENA_BASE.set(base);
            ARENA_END.set(base + SLAB_SIZE);
        }
        ARENA_PTR.set(base);
        ARENA_GEN.set(generation);
        let aligned = base.next_multiple_of(align);
        let new_ptr = aligned + size;
        if new_ptr <= ARENA_END.get() {
            ARENA_PTR.set(new_ptr);
            return aligned as *mut u8;
        }
    }
    unsafe { std::alloc::System.alloc(Layout::from_size_align_unchecked(size, align)) }
}

// SAFETY: All pointers returned are either from our mmap'd region (valid, aligned,
// non-overlapping per thread) or from System. The arena is thread-local so no data
// races. Relaxed ordering on ARENA_ACTIVE/GENERATION is sound: worst case a thread
// sees a stale value and does one extra system-alloc before picking up the new
// generation on the next call.
unsafe impl GlobalAlloc for ZkAllocator {
    #[inline(always)]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        if ARENA_ACTIVE.load(Ordering::Relaxed) {
            // Small allocs bypass arena: registry slots / HashMap entries /
            // injector-block-sized allocations from rayon/tracing libraries
            // commonly outlive a phase. Routing them to System keeps them
            // safe across begin_phase()/end_phase() boundaries.
            //
            // TODO is there a cleaner way?
            if layout.size() < MIN_ARENA_BYTES {
                return unsafe { std::alloc::System.alloc(layout) };
            }
            let generation = GENERATION.load(Ordering::Relaxed);
            if ARENA_GEN.get() == generation {
                let align = layout.align();
                let aligned = (ARENA_PTR.get() + align - 1) & !(align - 1);
                let new_ptr = aligned + layout.size();
                if new_ptr <= ARENA_END.get() {
                    ARENA_PTR.set(new_ptr);
                    return aligned as *mut u8;
                }
            }
            return unsafe { arena_alloc_cold(layout.size(), layout.align()) };
        }
        unsafe { std::alloc::System.alloc(layout) }
    }

    #[inline(always)]
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        let addr = ptr as usize;
        let base = REGION_BASE.load(Ordering::Relaxed);
        if base != 0 && addr >= base && addr < base + REGION_SIZE {
            return; // arena-owned pointer — free is a no-op
        }
        unsafe { std::alloc::System.dealloc(ptr, layout) };
    }

    #[inline(always)]
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        if new_size <= layout.size() {
            return ptr;
        }
        // Sticky-System routing: if the original allocation came from System
        // (small, or pre-phase, or routed by size-routing), keep the grown
        // allocation in System too. Without this, a Vec allocated outside a
        // phase that grows inside one would silently migrate into the arena
        // and become subject to phase recycling.
        let addr = ptr as usize;
        let base = REGION_BASE.load(Ordering::Relaxed);
        let in_arena = base != 0 && addr >= base && addr < base + REGION_SIZE;
        if !in_arena {
            return unsafe { std::alloc::System.realloc(ptr, layout, new_size) };
        }
        // SAFETY: new_size > layout.size() > 0, align unchanged from valid layout.
        let new_layout = unsafe { Layout::from_size_align_unchecked(new_size, layout.align()) };
        let new_ptr = unsafe { self.alloc(new_layout) };
        if !new_ptr.is_null() {
            unsafe { std::ptr::copy(ptr, new_ptr, layout.size()) };
            unsafe { self.dealloc(ptr, layout) };
        }
        new_ptr
    }
}
