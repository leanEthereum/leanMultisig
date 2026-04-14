use lean_multisig::{AggregatedXMSS, AggregationTopology, setup_prover, xmss_aggregate, xmss_verify_aggregation};
use leansig_wrapper::{MESSAGE_LENGTH, xmss_keygen_fast, xmss_sign_fast, xmss_verify};
use rand::{SeedableRng, rngs::StdRng};
use rec_aggregation::{benchmark::run_aggregation_benchmark, signatures_cache::{BENCHMARK_MESSAGE, BENCHMARK_SLOT, get_benchmark_signatures}};
use utils::decode_hex;

fn verify_test_vector(filename: &str) {
    use leansig_wrapper::{xmss_public_key_from_ssz, xmss_signature_from_ssz};

    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/test_vectors")
        .join(filename);
    let json: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap();

    let pk_bytes = decode_hex(json["public_key"].as_str().unwrap());
    let pk = xmss_public_key_from_ssz(&pk_bytes).unwrap();

    let slot = json["slot"].as_u64().unwrap() as u32;

    let msg_bytes = decode_hex(json["message"].as_str().unwrap());
    let mut message = [0u8; MESSAGE_LENGTH];
    message[..msg_bytes.len()].copy_from_slice(&msg_bytes);

    let sig_bytes = decode_hex(json["signature_ssz"].as_str().unwrap());
    let sig = xmss_signature_from_ssz(&sig_bytes).unwrap();

    xmss_verify(&pk, slot, &message, &sig).expect("test vector verify failed");
}

#[cfg(feature = "test-config")]
#[test]
fn test_xmss_test_vector() {
    verify_test_vector("xmss_test_vector.json");
}

#[cfg(not(feature = "test-config"))]
#[test]
fn test_xmss_prod_vector() {
    verify_test_vector("xmss_prod_test_vector.json");
}

#[test]
fn test_xmss_signature() {
    let activation_epoch = 111;
    let num_active_epochs = 39;
    let slot = 124;
    let mut rng: StdRng = StdRng::seed_from_u64(0);
    let message_hash: [u8; MESSAGE_LENGTH] = std::array::from_fn(|i| i as u8);

    let (secret_key, pub_key) = xmss_keygen_fast(&mut rng, activation_epoch, num_active_epochs);
    let signature = xmss_sign_fast(&secret_key, &message_hash, slot).unwrap();
    xmss_verify(&pub_key, slot, &message_hash, &signature).unwrap();
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
    let message = BENCHMARK_MESSAGE;
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

    xmss_verify_aggregation(final_pub_keys, &deserialized_final, &message, slot).unwrap();
}
