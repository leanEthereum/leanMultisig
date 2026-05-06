//! Regression test for arena/rayon corruption: rayon's `crossbeam_deque::Injector`
//! blocks (~1.5 KB) used to land in the arena and outlive a phase. Now prevented
//! by `MIN_ARENA_BYTES` size-routing in `ZkAllocator::alloc`.

use rayon::prelude::*;

#[global_allocator]
static A: zk_alloc::ZkAllocator = zk_alloc::ZkAllocator;

#[test]
fn rayon_does_not_corrupt_zkalloc() {
    zk_alloc::init();
    let _: u64 = (0..1_000_000_u64).into_par_iter().sum();

    zk_alloc::begin_phase();
    for _ in 0..200 {
        rayon::join(|| {}, || {});
    }
    zk_alloc::end_phase();

    zk_alloc::begin_phase();
    let canary = vec![0xAB_u8; 8192];
    rayon::join(|| {}, || {});
    zk_alloc::end_phase();

    let pos = canary.iter().position(|&b| b != 0xAB);
    assert!(pos.is_none(), "canary corrupted at offset {}", pos.unwrap());
}
