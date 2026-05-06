use lean_multisig::{aggregate_type_1, merge_many_type_1, setup_prover, split_type_2, verify_type_1, verify_type_2};
use xmss::signers_cache::{BENCHMARK_SLOT, get_benchmark_signatures, message_for_benchmark};

#[test]
fn test_type2_real_snark_merge() {
    setup_prover();

    let log_inv_rate = 2;
    let slot: u32 = BENCHMARK_SLOT;
    let message = message_for_benchmark();
    let signatures = get_benchmark_signatures();

    let raws_a = signatures[0..3].to_vec();
    let raws_b = signatures[3..5].to_vec();

    let type1_a = aggregate_type_1(&[], raws_a, message, slot, log_inv_rate).unwrap();
    let type1_b = aggregate_type_1(&[], raws_b, message, slot, log_inv_rate).unwrap();

    verify_type_1(&type1_a).unwrap();
    verify_type_1(&type1_b).unwrap();

    let info_a = type1_a.info.clone();
    let info_b = type1_b.info.clone();

    let type2 = merge_many_type_1(vec![type1_a, type1_b], log_inv_rate).unwrap();
    assert_eq!(type2.info.len(), 2);
    assert_eq!(type2.info[0], info_a);
    assert_eq!(type2.info[1], info_b);
    verify_type_2(&type2).unwrap();

    // Split round-trip: extract each component back into a type-1 multi-signature.
    let t = std::time::Instant::now();
    let split_a = split_type_2(type2.clone(), 0, log_inv_rate).unwrap();
    println!("split index 0: {:.2}s", t.elapsed().as_secs_f64());
    let t = std::time::Instant::now();
    let split_b = split_type_2(type2.clone(), 1, log_inv_rate).unwrap();
    println!("split index 1: {:.2}s", t.elapsed().as_secs_f64());
    // The split SNARK produces a fresh bytecode_claim, so only the user-facing
    // (message, slot, pubkeys) parts of the info are preserved.
    assert_eq!(split_a.info.message, info_a.message);
    assert_eq!(split_a.info.slot, info_a.slot);
    assert_eq!(split_a.info.pubkeys, info_a.pubkeys);
    assert_eq!(split_b.info.message, info_b.message);
    assert_eq!(split_b.info.slot, info_b.slot);
    assert_eq!(split_b.info.pubkeys, info_b.pubkeys);
    verify_type_1(&split_a).expect("split index 0 failed verify_type_1");
    verify_type_1(&split_b).expect("split index 1 failed verify_type_1");

    // Sanity: a split for component 0 must NOT verify against component 1's info.
    let mut wrong = split_a;
    wrong.info.pubkeys = info_b.pubkeys;
    wrong.info.message = info_b.message;
    wrong.info.slot = info_b.slot;
    assert!(verify_type_1(&wrong).is_err());

    // Tamper detection: changing one component's claimed slot must make
    // verify_type_2 fail (different public input → proof no longer matches).
    let mut tampered = type2;
    tampered.info[0].slot = tampered.info[0].slot.wrapping_add(1);
    assert!(verify_type_2(&tampered).is_err());
}
