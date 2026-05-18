use lean_multisig::{ZkAllocator, aggregate_type_1, begin_phase, end_phase, setup_prover, verify_type_1};
use xmss::signers_cache::{BENCHMARK_SLOT, get_benchmark_signatures, message_for_benchmark};

#[global_allocator]
static ALLOC: ZkAllocator = ZkAllocator;

#[test]
#[allow(clippy::redundant_clone)]
fn test_aggregation_with_zk_alloc() {
    setup_prover();

    let log_inv_rate = 2;
    let message = message_for_benchmark();
    let slot: u32 = BENCHMARK_SLOT;
    let signatures = get_benchmark_signatures();
    let raw_xmss = signatures[0..6].to_vec();

    begin_phase();
    let aggregated = aggregate_type_1(&[], raw_xmss, message, slot, log_inv_rate).unwrap();
    end_phase();
    // IMPORTANT: clone to move the data out of the arena memory
    let aggregated = aggregated.clone();

    verify_type_1(&aggregated).unwrap();
}
