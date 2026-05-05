use lean_multisig::{ZkAllocator, begin_phase, end_phase, setup_prover, xmss_aggregate, xmss_verify_aggregation};
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
    let pub_keys_and_sigs = signatures[0..6].to_vec();

    begin_phase();
    let (pub_keys, aggregated) = xmss_aggregate(&[], pub_keys_and_sigs, &message, slot, log_inv_rate).unwrap();
    end_phase();
    // IMPORTANT: clone to move the data out of the arena memory
    let (pub_keys, aggregated) = (pub_keys.clone(), aggregated.clone());

    xmss_verify_aggregation(&pub_keys, &aggregated, &message, slot).unwrap();
}
