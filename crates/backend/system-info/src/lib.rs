include!(concat!(env!("OUT_DIR"), "/info.rs"));

const _: () = assert!(usize::BITS == 64, "this project requires a 64-bit target (for now)");

pub fn peak_rss_bytes() -> u64 {
    let mut ru: libc::rusage = unsafe { std::mem::zeroed() };
    unsafe { libc::getrusage(libc::RUSAGE_SELF, &raw mut ru) };
    let max = ru.ru_maxrss as u64;
    // ru_maxrss unit: bytes on macOS, KiB on Linux.
    if cfg!(target_os = "macos") { max } else { max * 1024 }
}

/// Number of jobs [`flush_rayon`] pushes. Must exceed
/// `crossbeam_deque::deque::BLOCK_CAP` (currently 63 —
/// `crossbeam-deque-0.8.6/src/deque.rs:1191`).
const RAYON_FLUSH_JOBS: usize = 256;

/// Drain rayon's internal queues so they release any storage allocated during the
/// previous phase.
///
/// Rayon's global pool owns a `crossbeam_deque::Injector`, internally a linked list
/// of fixed-size blocks (`Block` and `Injector::push` —
/// `crossbeam-deque-0.8.6/src/deque.rs:1219` and `:1371`). A block is freed only
/// once its last slot has been consumed.
///
/// `rayon::join` from a non-worker thread reaches that injector via
/// `join` (`rayon-core-1.13.0/src/join/mod.rs:132`) ->
/// `registry::in_worker` (`registry.rs:946`) ->
/// `Registry::in_worker_cold` (`:517`) ->
/// `Registry::inject` (`:428`) -> `Injector::push`.
///
/// Under an arena allocator that recycles memory between phases (e.g. `zk-alloc`),
/// a block allocated *during* a phase points into a slab the next `begin_phase()`
/// will reuse. The next push then writes a `JobRef` straight through whatever the
/// application has placed on top, silently corrupting it.
///
/// Pushing more than `BLOCK_CAP` jobs while the arena is off forces the Injector                                        
/// to allocate a fresh tail block (which lands in System), and forces workers to                                      
/// steal the last slot of every preceding block (which destroys them).
pub fn flush_rayon() {
    for _ in 0..RAYON_FLUSH_JOBS {
        rayon::join(|| {}, || {});
    }
}
