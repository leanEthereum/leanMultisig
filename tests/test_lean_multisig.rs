use lean_multisig::{AggregatedXMSS, AggregationTopology, setup_prover, xmss_aggregate, xmss_verify_aggregation};
use rand::{RngExt, SeedableRng, rngs::StdRng};
use rec_aggregation::benchmark::run_aggregation_benchmark;
use xmss::{
    signers_cache::{BENCHMARK_SLOT, get_benchmark_signatures, message_for_benchmark},
    xmss_key_gen, xmss_sign, xmss_verify,
};

#[test]
fn test_xmss_signature() {
    let start_slot = 111;
    let end_slot = 200;
    let slot: u32 = 124;
    let mut rng: StdRng = StdRng::seed_from_u64(0);
    let msg = rng.random();

    let (secret_key, pub_key) = xmss_key_gen(rng.random(), start_slot, end_slot).unwrap();
    let signature = xmss_sign(&mut rng, &secret_key, &msg, slot).unwrap();
    xmss_verify(&pub_key, &msg, &signature, slot).unwrap();
}

#[test]
fn test_aggregation() {
    for n_signatures in [1, 2, 4, 8, 16, 32, 64, 128] {
        let topology = AggregationTopology {
            raw_xmss: n_signatures,
            children: vec![],
            log_inv_rate: 1,
        };
        run_aggregation_benchmark(&topology, 0, false);
    }
}

#[test]
fn test_recursive_aggregation() {
    setup_prover();

    let log_inv_rate = 2; // [1, 2, 3 or 4] (lower = faster but bigger proofs)
    let message = message_for_benchmark();
    let slot: u32 = BENCHMARK_SLOT;
    let signatures = get_benchmark_signatures();

    let pub_keys_and_sigs_a = signatures[0..3].to_vec();
    let (pub_keys_a, aggregated_a) = xmss_aggregate(&[], pub_keys_and_sigs_a, &message, slot, log_inv_rate);

    let pub_keys_and_sigs_b = signatures[3..5].to_vec();
    let (pub_keys_b, aggregated_b) = xmss_aggregate(&[], pub_keys_and_sigs_b, &message, slot, log_inv_rate);

    let pub_keys_and_sigs_c = signatures[5..6].to_vec();

    let children: Vec<(&[_], AggregatedXMSS)> = vec![(&pub_keys_a, aggregated_a), (&pub_keys_b, aggregated_b)];
    let (final_pub_keys, aggregated_final) =
        xmss_aggregate(&children, pub_keys_and_sigs_c, &message, slot, log_inv_rate);

    let serialized_final = aggregated_final.serialize();
    println!("Serialized aggregated final: {} KiB", serialized_final.len() / 1024);
    let deserialized_final = AggregatedXMSS::deserialize(&serialized_final).unwrap();

    xmss_verify_aggregation(&final_pub_keys, &deserialized_final, &message, slot).unwrap();
}
