use lean_multisig::{TypeOneMultiSignature, aggregate_type_1, setup_prover, verify_type_1};
use rand::{RngExt, SeedableRng, rngs::StdRng};
use rec_aggregation::benchmark::{AggregationTopology, run_aggregation_benchmark};
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
            overlap: 0,
        };
        run_aggregation_benchmark(&topology, false, true);
    }
}

#[test]
fn test_recursive_aggregation() {
    setup_prover();

    let log_inv_rate = 2; // [1, 2, 3 or 4] (lower = faster but bigger proofs)
    let message = message_for_benchmark();
    let slot: u32 = BENCHMARK_SLOT;
    let signatures = get_benchmark_signatures();

    let raws_a = signatures[0..3].to_vec();
    let type1_a = aggregate_type_1(&[], raws_a, message, slot, log_inv_rate).unwrap();

    let raws_b = signatures[3..5].to_vec();
    let type1_b = aggregate_type_1(&[], raws_b, message, slot, log_inv_rate).unwrap();

    let raws_c = signatures[5..6].to_vec();
    let final_sig = aggregate_type_1(&[type1_a, type1_b], raws_c, message, slot, log_inv_rate).unwrap();

    let serialized_proof = final_sig.compress();
    println!("Serialized aggregated final: {} KiB", serialized_proof.len() / 1024);
    let recovered = TypeOneMultiSignature::decompress(&serialized_proof).unwrap();

    verify_type_1(&recovered).unwrap();
}
