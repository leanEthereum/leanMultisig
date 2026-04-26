use std::alloc::{GlobalAlloc, Layout};
use std::cell::Cell;
use std::sync::Once;
use std::sync::atomic::{AtomicUsize, Ordering};

mod syscall;

#[derive(Debug)]
pub struct ZkAllocator;

static GENERATION: AtomicUsize = AtomicUsize::new(0);
static ALLOC_IMPL: AtomicUsize = AtomicUsize::new(0);
static WARMUP_DONE: AtomicUsize = AtomicUsize::new(0);

const SLAB_SIZE: usize = 8 * 1024 * 1024 * 1024; // 8GB
const MAX_THREADS: usize = 16;
const REGION_SIZE: usize = SLAB_SIZE * MAX_THREADS;

static REGION_BASE: AtomicUsize = AtomicUsize::new(0);
static REGION_INIT: Once = Once::new();
static THREAD_IDX: AtomicUsize = AtomicUsize::new(0);

fn ensure_region() -> usize {
    REGION_INIT.call_once(|| {
        // SAFETY: mmap_anonymous returns a page-aligned pointer or null.
        // MAP_NORESERVE means no physical memory is committed yet.
        let ptr = unsafe { syscall::mmap_anonymous(REGION_SIZE, false) };
        if ptr.is_null() {
            std::process::abort();
        }
        unsafe { syscall::madvise(ptr, REGION_SIZE, syscall::MADV_HUGEPAGE) };
        REGION_BASE.store(ptr as usize, Ordering::Release);
    });
    REGION_BASE.load(Ordering::Acquire)
}

thread_local! {
    static ARENA_PTR: Cell<usize> = const { Cell::new(0) };
    static ARENA_END: Cell<usize> = const { Cell::new(0) };
    static ARENA_BASE: Cell<usize> = const { Cell::new(0) };
    static ARENA_GEN: Cell<usize> = const { Cell::new(0) };
}

pub fn phase_boundary() {
    let prev = WARMUP_DONE.load(Ordering::Relaxed);
    if prev == 0 {
        WARMUP_DONE.store(1, Ordering::Relaxed);
        return;
    }
    GENERATION.fetch_add(1, Ordering::Release);
    ALLOC_IMPL.store(1, Ordering::Release);
}

pub fn deactivate_arena() {
    ALLOC_IMPL.store(0, Ordering::Release);
}

#[cold]
#[inline(never)]
unsafe fn arena_alloc_cold(size: usize, align: usize) -> *mut u8 {
    let generation = GENERATION.load(Ordering::Relaxed);
    if ARENA_GEN.get() != generation {
        let base = ARENA_BASE.get();
        if base != 0 {
            // Generation changed — reset bump pointer to slab base.
            ARENA_PTR.set(base);
            ARENA_GEN.set(generation);
            let aligned = (base + align - 1) & !(align - 1);
            let new_ptr = aligned + size;
            if new_ptr <= ARENA_END.get() {
                ARENA_PTR.set(new_ptr);
                return aligned as *mut u8;
            }
        } else {
            // First allocation on this thread — claim a slab.
            let region = ensure_region();
            let idx = THREAD_IDX.fetch_add(1, Ordering::Relaxed);
            if idx >= MAX_THREADS {
                ARENA_BASE.set(1); // sentinel: this thread has no slab
                // SAFETY: size and align are from a valid Layout (caller contract).
                return unsafe { std::alloc::System.alloc(Layout::from_size_align_unchecked(size, align)) };
            }
            let slab_base = region + idx * SLAB_SIZE;
            ARENA_BASE.set(slab_base);
            ARENA_END.set(slab_base + SLAB_SIZE);
            ARENA_GEN.set(generation);

            let aligned = (slab_base + align - 1) & !(align - 1);
            let new_ptr = aligned + size;
            if new_ptr <= slab_base + SLAB_SIZE {
                ARENA_PTR.set(new_ptr);
                return aligned as *mut u8;
            }
        }
    }
    // SAFETY: size and align are from a valid Layout (caller contract).
    unsafe { std::alloc::System.alloc(Layout::from_size_align_unchecked(size, align)) }
}

// SAFETY: All pointers returned are either from our mmap'd region (valid, aligned,
// non-overlapping per thread) or from System. The arena is thread-local so no data
// races. Relaxed ordering on ALLOC_IMPL/GENERATION is sound: worst case a thread
// sees a stale value and does one extra system-alloc before picking up the new
// generation on the next call.
unsafe impl GlobalAlloc for ZkAllocator {
    #[inline(always)]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let active = ALLOC_IMPL.load(Ordering::Relaxed);
        if active != 0 {
            let generation = GENERATION.load(Ordering::Relaxed);
            if ARENA_GEN.get() == generation {
                let ptr = ARENA_PTR.get();
                let aligned = (ptr + layout.align() - 1) & !(layout.align() - 1);
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
        // SAFETY: new_size > layout.size() > 0, align unchanged from valid layout.
        let new_layout = unsafe { Layout::from_size_align_unchecked(new_size, layout.align()) };
        let new_ptr = unsafe { self.alloc(new_layout) };
        if !new_ptr.is_null() {
            unsafe { std::ptr::copy_nonoverlapping(ptr, new_ptr, layout.size()) };
            unsafe { self.dealloc(ptr, layout) };
        }
        new_ptr
    }
}
