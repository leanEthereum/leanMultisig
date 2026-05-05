//! Regression test for the bug `system_info::flush_rayon` exists to prevent.
//!
//! Without `flush_rayon` (called by `end_phase`), the `rayon::join` in phase 2
//! writes a `JobRef` into the freshly-allocated canary buffer, because the
//! `crossbeam_deque::Injector`'s tail block was still pointing into the slab
//! reset by `begin_phase`. With the fix, the canary survives untouched.

use rayon::prelude::*;

#[global_allocator]
static A: zk_alloc::ZkAllocator = zk_alloc::ZkAllocator;

#[test]
fn arena_reset_does_not_corrupt_user_data() {
    // Warm rayon up while the arena is off, so worker deques live in System.
    zk_alloc::init();
    let _: u64 = (0..1_000_000_u64).into_par_iter().sum();

    // Phase 1: enough top-level joins to make `Injector::push` allocate at least
    // one fresh block while the arena is on, so it lands inside the slab.
    zk_alloc::begin_phase();
    for _ in 0..200 {
        rayon::join(|| {}, || {});
    }
    zk_alloc::end_phase();

    // Phase 2: drop a canary at the start of the just-reset slab and force one
    // more inject. Without the fix, the push corrupts the canary.
    zk_alloc::begin_phase();
    let canary = vec![0xAB_u8; 8192];
    rayon::join(|| {}, || {});
    zk_alloc::end_phase();

    let pos = canary.iter().position(|&b| b != 0xAB);
    assert!(pos.is_none(), "canary corrupted at offset {}", pos.unwrap());
}
