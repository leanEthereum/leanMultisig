use std::time::Instant;

use lean_multisig::{
    TypeOneMultiSignature, TypeTwoMultiSignature, aggregate_type_1, merge_many_type_1, setup_prover, split_type_2,
    verify_type_1, verify_type_2,
};
use leansig_wrapper::{xmss_keygen_fast, xmss_sign_fast, xmss_verify};
use rand::{RngExt, SeedableRng, rngs::StdRng};
use rec_aggregation::benchmark::{AggregationTopology, run_aggregation_benchmark};
use rec_aggregation::signatures_cache::{BENCHMARK_SLOT, get_benchmark_signatures, message_for_benchmark};
use rec_aggregation::split_type_2_by_msg;

#[test]
fn test_xmss_signature() {
    let activation_epoch = 111;
    let num_active_epochs = 39;
    let slot: u32 = 124;
    let mut rng: StdRng = StdRng::seed_from_u64(0);
    let msg = [42u8; leansig_wrapper::MESSAGE_LENGTH];

    let (secret_key, pub_key) = xmss_keygen_fast(&mut rng, activation_epoch, num_active_epochs);
    let signature = xmss_sign_fast(&secret_key, &msg, slot).unwrap();
    xmss_verify(&pub_key, slot, &msg, &signature).unwrap();
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
fn test_type_1_aggregation() {
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

#[test]
fn test_type_2_aggregation() {
    setup_prover();

    let log_inv_rate = 2; // [1, 2, 3 or 4] (lower = faster but bigger proofs)
    let slot_a = BENCHMARK_SLOT;
    let message_a = message_for_benchmark();
    let signatures = get_benchmark_signatures();
    let raws_a = signatures[0..3].to_vec();

    let slot_b = BENCHMARK_SLOT + 1;
    let mut rng_b: StdRng = StdRng::seed_from_u64(17);
    let message_b: [u8; leansig_wrapper::MESSAGE_LENGTH] = std::array::from_fn(|_| rng_b.random());

    assert!(message_b != message_a && slot_b != slot_a);

    let raws_b: Vec<_> = (0..2)
        .map(|_| {
            let (sk, pk) = xmss_keygen_fast(&mut rng_b, slot_b, 1);
            let sig = xmss_sign_fast(&sk, &message_b, slot_b).unwrap();
            (pk, sig)
        })
        .collect();

    let type1_a = aggregate_type_1(&[], raws_a, message_a, slot_a, log_inv_rate).unwrap();
    let type1_b = aggregate_type_1(&[], raws_b, message_b, slot_b, log_inv_rate).unwrap();

    verify_type_1(&type1_a).unwrap();
    verify_type_1(&type1_b).unwrap();

    let info_a = type1_a.info.clone();
    let info_b = type1_b.info.clone();

    let time = Instant::now();
    let type2 = merge_many_type_1(vec![type1_a, type1_b], log_inv_rate).unwrap();
    println!("merge_many_type_1: {:.2}s", time.elapsed().as_secs_f64());
    assert_eq!(type2.info.len(), 2);
    assert_eq!(type2.info[0], info_a);
    assert_eq!(type2.info[1], info_b);

    verify_type_2(&type2).unwrap();

    let time = Instant::now();
    let split_a = split_type_2(type2.clone(), 0, log_inv_rate).unwrap();
    println!("split index 0: {:.2}s", time.elapsed().as_secs_f64());
    let time = Instant::now();
    let split_b = split_type_2_by_msg(type2, message_b, log_inv_rate).unwrap();
    println!("split index 1: {:.2}s", time.elapsed().as_secs_f64());
    assert_eq!(
        (
            split_a.info.without_pubkeys.message,
            &split_a.info.without_pubkeys.slot,
            &split_a.info.pubkeys,
        ),
        (
            info_a.without_pubkeys.message,
            &info_a.without_pubkeys.slot,
            &info_a.pubkeys,
        )
    );
    assert_eq!(
        (
            split_b.info.without_pubkeys.message,
            &split_b.info.without_pubkeys.slot,
            &split_b.info.pubkeys,
        ),
        (
            info_b.without_pubkeys.message,
            &info_b.without_pubkeys.slot,
            &info_b.pubkeys,
        )
    );
    verify_type_1(&split_a).expect("split index 0 failed verify_type_1");
    verify_type_1(&split_b).expect("split index 1 failed verify_type_1");
}

#[test]
fn test_type1_type2_compression() {
    setup_prover();

    let log_inv_rate = 2;
    let message = message_for_benchmark();
    let slot = BENCHMARK_SLOT;
    let signatures = get_benchmark_signatures();

    // The pubkey set is shared between prover and verifier.
    let raws_a = signatures[..3].to_vec();
    let mut shared_pubkeys_a = raws_a.iter().map(|(pk, _)| pk.clone()).collect::<Vec<_>>();
    shared_pubkeys_a.sort();
    let type1_a = aggregate_type_1(&[], raws_a, message, slot, log_inv_rate).unwrap();

    let type1_a_compressed_compact = type1_a.compress_without_pubkeys();
    let type1_a_compact_recovered =
        TypeOneMultiSignature::decompress_without_pubkeys(&type1_a_compressed_compact, shared_pubkeys_a)
            .expect("type-1 round-trip");
    verify_type_1(&type1_a_compact_recovered).expect("recovered type-1 must verify");
    assert_eq!(type1_a_compact_recovered.info.pubkeys, type1_a.info.pubkeys);

    let type1_a_compressed_full = type1_a.compress();
    let type1_a_full_recovered =
        TypeOneMultiSignature::decompress(&type1_a_compressed_full).expect("type-1 round-trip");
    verify_type_1(&type1_a_full_recovered).expect("recovered type-1 must verify");
    assert_eq!(type1_a_full_recovered.info.pubkeys, type1_a.info.pubkeys);

    assert!(type1_a_compressed_compact.len() < type1_a_compressed_full.len());

    let slot_b = BENCHMARK_SLOT + 1;
    let mut rng_b: StdRng = StdRng::seed_from_u64(17);
    let message_b: [u8; leansig_wrapper::MESSAGE_LENGTH] = std::array::from_fn(|_| rng_b.random());
    let raws_b: Vec<_> = (0..2)
        .map(|_| {
            let (sk, pk) = xmss_keygen_fast(&mut rng_b, slot_b, 1);
            let xs = xmss_sign_fast(&sk, &message_b, slot_b).unwrap();
            (pk, xs)
        })
        .collect();
    let type1_b = aggregate_type_1(&[], raws_b, message_b, slot_b, log_inv_rate).unwrap();

    let type2 = merge_many_type_1(vec![type1_a, type1_b], log_inv_rate).unwrap();
    let shared_pubkeys_type2: Vec<_> = type2.info.iter().map(|i| i.pubkeys.clone()).collect();

    let type2_compressed_compact = type2.compress_without_pubkeys();
    let type2_compact_recovered =
        TypeTwoMultiSignature::decompress_without_pubkeys(&type2_compressed_compact, shared_pubkeys_type2)
            .expect("type-2 round-trip");
    verify_type_2(&type2_compact_recovered).expect("recovered type-2 must verify");
    assert_eq!(type2_compact_recovered.info, type2.info);

    let type2_compressed_full = type2.compress();
    let type2_full_recovered = TypeTwoMultiSignature::decompress(&type2_compressed_full).expect("type-2 round-trip");
    verify_type_2(&type2_full_recovered).expect("recovered type-2 must verify");
    assert_eq!(type2_full_recovered.info, type2.info);

    assert!(type2_compressed_compact.len() < type2_compressed_full.len());
}
