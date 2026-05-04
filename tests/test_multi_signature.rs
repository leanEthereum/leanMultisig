use lean_multisig::{
    aggregate_type_1, merge_many_type_1, message_bytes_to_field, setup_prover, split_type_2, verify_type1, verify_type2,
};
use xmss::signers_cache::{BENCHMARK_SLOT, get_benchmark_signatures};

fn benchmark_message_bytes() -> [u8; 32] {
    // Round-trips with `message_for_benchmark()` so cached signatures (which were
    // signed against `message_for_benchmark()`) verify under the byte-encoded API.
    let mut bytes = [0u8; 32];
    for i in 0..8 {
        let v = i as u32;
        bytes[i * 4..i * 4 + 4].copy_from_slice(&v.to_le_bytes());
    }
    debug_assert_eq!(
        message_bytes_to_field(&bytes),
        xmss::signers_cache::message_for_benchmark()
    );
    bytes
}

#[test]
fn test_type2_real_snark_merge() {
    setup_prover();

    let log_inv_rate = 2;
    let slot: u32 = BENCHMARK_SLOT;
    let message = benchmark_message_bytes();
    let signatures = get_benchmark_signatures();

    let raws_a = signatures[0..3].to_vec();
    let raws_b = signatures[3..5].to_vec();

    let type1_a = aggregate_type_1(&[], raws_a, message, slot, log_inv_rate).unwrap();
    let type1_b = aggregate_type_1(&[], raws_b, message, slot, log_inv_rate).unwrap();

    assert!(verify_type1(&type1_a));
    assert!(verify_type1(&type1_b));

    let info_a = type1_a.info.clone();
    let info_b = type1_b.info.clone();

    let type2 = merge_many_type_1(vec![type1_a, type1_b], log_inv_rate).unwrap();
    assert_eq!(type2.info.len(), 2);
    assert_eq!(type2.info[0], info_a);
    assert_eq!(type2.info[1], info_b);
    assert!(verify_type2(&type2));

    // Split round-trip: extract each component back into a type-1 multi-signature.
    let t = std::time::Instant::now();
    let split_a = split_type_2(type2.clone(), 0, log_inv_rate).unwrap();
    println!("split index 0: {:.2}s", t.elapsed().as_secs_f64());
    let t = std::time::Instant::now();
    let split_b = split_type_2(type2.clone(), 1, log_inv_rate).unwrap();
    println!("split index 1: {:.2}s", t.elapsed().as_secs_f64());
    assert_eq!(split_a.info, info_a);
    assert_eq!(split_b.info, info_b);
    assert!(verify_type1(&split_a), "split index 0 failed verify_type1");
    assert!(verify_type1(&split_b), "split index 1 failed verify_type1");

    // Sanity: a split for component 0 must NOT verify against component 1's info.
    let mut wrong = split_a;
    wrong.info = info_b;
    assert!(!verify_type1(&wrong));

    // Tamper detection: changing one component's claimed slot must make
    // verify_type2 fail (different public input → proof no longer matches).
    let mut tampered = type2;
    tampered.info[0].slot = tampered.info[0].slot.wrapping_add(1);
    assert!(!verify_type2(&tampered));
}
