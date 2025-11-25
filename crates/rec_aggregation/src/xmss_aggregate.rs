use lean_compiler::*;
use lean_prover::{LOG_SMALLEST_DECOMPOSITION_CHUNK, whir_config_builder};
use lean_prover::{prove_execution::prove_execution, verify_execution::verify_execution};
use lean_vm::*;
use multilinear_toolkit::prelude::*;
use rand::{Rng, SeedableRng, rngs::StdRng};
use std::time::Instant;
use tracing::instrument;
use whir_p3::precompute_dft_twiddles;
use xmss::{PhonyXmssSecretKey, Poseidon16History, Poseidon24History, V, XmssPublicKey, XmssSignature};

const MAX_LOG_LIFETIME: usize = 30;

pub fn run_xmss_benchmark(n_xmss: usize) {
    // Public input:  message_hash | all_public_keys | bitield
    // Private input: signatures = (randomness | chain_tips | merkle_path)
    let mut program_str = r#"
    const COMPRESSION = 1;
    const PERMUTATION = 0;

    const V = 68;
    const W = 4;
    const TARGET_SUM = 114;
    const N_PUBLIC_KEYS = N_PUBLIC_KEYS_PLACE_HOLDER;
    const XMSS_SIG_SIZE = XMSS_SIG_SIZE_PLACE_HOLDER; // vectorized and padded

    fn main() {
        public_input_start_ = public_input_start;
        private_input_start = public_input_start_[0];
        message_hash = public_input_start / 8 + 1;
        all_public_keys = message_hash + 1;
        all_log_lifetimes = (all_public_keys + N_PUBLIC_KEYS) * 8;
        signatures_start = private_input_start / 8;
        for i in 0..N_PUBLIC_KEYS {
            xmss_public_key = all_public_keys + i;
            signature = signatures_start + i * XMSS_SIG_SIZE;
            log_lifetime = all_log_lifetimes[i];
            xmss_public_key_recovered = xmss_recover_pub_key(message_hash, signature, log_lifetime);
            assert_eq_vec(xmss_public_key, xmss_public_key_recovered);
        }
        return;
    }

    fn xmss_recover_pub_key(message_hash, signature, log_lifetime) -> 1 {
        // message_hash: vectorized pointers (of length 1)
        // signature: vectorized pointer = randomness | chain_tips | merkle_neighbours | merkle_are_left
        // return a vectorized pointer (of length 1), the hashed xmss public key
        randomness = signature; // vectorized
        chain_tips = signature + 1; // vectorized
        merkle_neighbours = chain_tips + V; // vectorized
        merkle_are_left = (merkle_neighbours + log_lifetime) * 8; // non-vectorized

        // 1) We encode message_hash + randomness into the d-th layer of the hypercube

        compressed = malloc_vec(1);
        poseidon16(message_hash, randomness, compressed, COMPRESSION);
        compressed_ptr = compressed * 8;
        decomposed = decompose_custom(compressed_ptr[0], compressed_ptr[1], compressed_ptr[2], compressed_ptr[3], compressed_ptr[4], compressed_ptr[5]);
        
        // check that the decomposition is correct
        for i in 0..6 unroll {
            for j in 0..12 unroll {
                // TODO Implem range check (https://github.com/leanEthereum/leanMultisig/issues/52)
                // For now we use dummy instructions to replicate exactly the cost

                // assert decomposed[i * 13 + j] < 4;
                dummy_0 = 88888888;
                assert dummy_0 == 88888888;
                assert dummy_0 == 88888888;
                assert dummy_0 == 88888888;
            }

            // assert decomposed[i * 13 + 12] < 2^7 - 1;
            dummy_1 = 88888888;
            dummy_2 = 88888888;
            dummy_3 = 88888888;
            assert dummy_1 == 88888888;
            assert dummy_2 == 88888888;
            assert dummy_3 == 88888888;

            partial_sums = malloc(12);
            partial_sums[0] = decomposed[i * 13];
            for j in 1..12 unroll {
                partial_sums[j] = partial_sums[j - 1] + (decomposed[i * 13 + j]) * 4**j;
            }
            assert partial_sums[11] + (decomposed[i * 13 + 12]) * 4**12 == compressed_ptr[i];
        }
        
        encoding = malloc(12 * 6);
        for i in 0..6 unroll {
            for j in 0..12 unroll {
                encoding[i * 12 + j] = decomposed[i * 13 + j];
            }
        }

        // we need to check the target sum
        sums = malloc(V);
        sums[0] = encoding[0];
        for i in 1..V unroll {
            sums[i] = sums[i - 1] + encoding[i];
        }
        assert sums[V - 1] == TARGET_SUM;

        public_key = malloc_vec(V);

        chain_tips_ptr = 8 * chain_tips;
        public_key_ptr = 8 * public_key;

        for i in 0..V unroll {
            match encoding[i] {
                0 => {
                    var_1 = chain_tips + i;
                    var_2 = public_key + i;
                    var_3 = malloc_vec(1);
                    var_4 = malloc_vec(1);
                    poseidon16(var_1, pointer_to_zero_vector, var_3, COMPRESSION);
                    poseidon16(var_3, pointer_to_zero_vector, var_4, COMPRESSION);
                    poseidon16(var_4, pointer_to_zero_vector, var_2, COMPRESSION);
                }
                1 => {
                    var_3 = malloc_vec(1);
                    var_1 = chain_tips + i;
                    var_2 = public_key + i;
                    poseidon16(var_1, pointer_to_zero_vector, var_3, COMPRESSION);
                    poseidon16(var_3, pointer_to_zero_vector, var_2, COMPRESSION);
                }
                2 => {
                    var_1 = chain_tips + i;
                    var_2 = public_key + i;
                    poseidon16(var_1, pointer_to_zero_vector, var_2, COMPRESSION);
                }
                3 => {
                    var_1 = chain_tips_ptr + (i * 8);
                    var_2 = public_key_ptr + (i * 8);
                    var_3 = var_1 + 3;
                    var_4 = var_2 + 3;
                    dot_product_ee(var_1, pointer_to_one_vector * 8, var_2, 1);
                    dot_product_ee(var_3, pointer_to_one_vector * 8, var_4, 1);
                }
            }
        }

        public_key_hashed = malloc_vec(V / 2);
        poseidon24(public_key, pointer_to_zero_vector, public_key_hashed);

        for i in 1..V / 2 unroll {
            poseidon24(public_key + (2*i), public_key_hashed + (i - 1), public_key_hashed + i);
        }

        wots_pubkey_hashed = public_key_hashed + (V / 2 - 1);

        // TODO unroll
        match log_lifetime {
            0 => { merkle_hash = verify_merkle_path(0, merkle_are_left, wots_pubkey_hashed, merkle_neighbours); }
            1 => { merkle_hash = verify_merkle_path(1, merkle_are_left, wots_pubkey_hashed, merkle_neighbours); }
            2 => { merkle_hash = verify_merkle_path(2, merkle_are_left, wots_pubkey_hashed, merkle_neighbours); }
            3 => { merkle_hash = verify_merkle_path(3, merkle_are_left, wots_pubkey_hashed, merkle_neighbours); }
            4 => { merkle_hash = verify_merkle_path(4, merkle_are_left, wots_pubkey_hashed, merkle_neighbours); }
            5 => { merkle_hash = verify_merkle_path(5, merkle_are_left, wots_pubkey_hashed, merkle_neighbours); }
            6 => { merkle_hash = verify_merkle_path(6, merkle_are_left, wots_pubkey_hashed, merkle_neighbours); }
            7 => { merkle_hash = verify_merkle_path(7, merkle_are_left, wots_pubkey_hashed, merkle_neighbours); }
            8 => { merkle_hash = verify_merkle_path(8, merkle_are_left, wots_pubkey_hashed, merkle_neighbours); }
            9 => { merkle_hash = verify_merkle_path(9, merkle_are_left, wots_pubkey_hashed, merkle_neighbours); }
            10 => { merkle_hash = verify_merkle_path(10, merkle_are_left, wots_pubkey_hashed, merkle_neighbours); }
            11 => { merkle_hash = verify_merkle_path(11, merkle_are_left, wots_pubkey_hashed, merkle_neighbours); }
            12 => { merkle_hash = verify_merkle_path(12, merkle_are_left, wots_pubkey_hashed, merkle_neighbours); }
            13 => { merkle_hash = verify_merkle_path(13, merkle_are_left, wots_pubkey_hashed, merkle_neighbours); }
            14 => { merkle_hash = verify_merkle_path(14, merkle_are_left, wots_pubkey_hashed, merkle_neighbours); }
            15 => { merkle_hash = verify_merkle_path(15, merkle_are_left, wots_pubkey_hashed, merkle_neighbours); }
            16 => { merkle_hash = verify_merkle_path(16, merkle_are_left, wots_pubkey_hashed, merkle_neighbours); }
            17 => { merkle_hash = verify_merkle_path(17, merkle_are_left, wots_pubkey_hashed, merkle_neighbours); }
            18 => { merkle_hash = verify_merkle_path(18, merkle_are_left, wots_pubkey_hashed, merkle_neighbours); }
            19 => { merkle_hash = verify_merkle_path(19, merkle_are_left, wots_pubkey_hashed, merkle_neighbours); }
            20 => { merkle_hash = verify_merkle_path(20, merkle_are_left, wots_pubkey_hashed, merkle_neighbours); }
            21 => { merkle_hash = verify_merkle_path(21, merkle_are_left, wots_pubkey_hashed, merkle_neighbours); }
            22 => { merkle_hash = verify_merkle_path(22, merkle_are_left, wots_pubkey_hashed, merkle_neighbours); }
            23 => { merkle_hash = verify_merkle_path(23, merkle_are_left, wots_pubkey_hashed, merkle_neighbours); }
            24 => { merkle_hash = verify_merkle_path(24, merkle_are_left, wots_pubkey_hashed, merkle_neighbours); }
            25 => { merkle_hash = verify_merkle_path(25, merkle_are_left, wots_pubkey_hashed, merkle_neighbours); }
            26 => { merkle_hash = verify_merkle_path(26, merkle_are_left, wots_pubkey_hashed, merkle_neighbours); }
            27 => { merkle_hash = verify_merkle_path(27, merkle_are_left, wots_pubkey_hashed, merkle_neighbours); }
            28 => { merkle_hash = verify_merkle_path(28, merkle_are_left, wots_pubkey_hashed, merkle_neighbours); }
            29 => { merkle_hash = verify_merkle_path(29, merkle_are_left, wots_pubkey_hashed, merkle_neighbours); }
            30 => { merkle_hash = verify_merkle_path(30, merkle_are_left, wots_pubkey_hashed, merkle_neighbours); }
            31 => { merkle_hash = verify_merkle_path(31, merkle_are_left, wots_pubkey_hashed, merkle_neighbours); }
            32 => { merkle_hash = verify_merkle_path(32, merkle_are_left, wots_pubkey_hashed, merkle_neighbours); }
        }

        return merkle_hash;
    }

    fn verify_merkle_path(const height, merkle_are_left, leaf_hash, merkle_neighbours) -> 1 {
        merkle_hashes = malloc_vec(height);
        if merkle_are_left[0] == 1 {
            poseidon16(leaf_hash, merkle_neighbours, merkle_hashes, COMPRESSION);
        } else {
            poseidon16(merkle_neighbours, leaf_hash, merkle_hashes, COMPRESSION);
        }
        for h in 1..log_lifetime {
            if merkle_are_left[h] == 1 {
                poseidon16(merkle_hashes + (h-1), merkle_neighbours + h, merkle_hashes + h, COMPRESSION);
            } else {
                poseidon16(merkle_neighbours + h, merkle_hashes + (h-1), merkle_hashes + h, COMPRESSION);
            }
        }
        return merkle_hashes + (log_lifetime - 1);
    }

    fn assert_eq_vec(x, y) inline {
        // x and y are vectorized pointer of len 1 each
        ptr_x = x * 8;
        ptr_y = y * 8;
        dot_product_ee(ptr_x, pointer_to_one_vector * 8, ptr_y, 1);
        dot_product_ee(ptr_x + 3, pointer_to_one_vector * 8, ptr_y + 3, 1);
        return;
    }
   "#.to_string();

    let xmss_signature_size_padded = (V + 1 + MAX_LOG_LIFETIME) + MAX_LOG_LIFETIME.div_ceil(8);
    program_str = program_str
        .replace("N_PUBLIC_KEYS_PLACE_HOLDER", &n_xmss.to_string())
        .replace("XMSS_SIG_SIZE_PLACE_HOLDER", &xmss_signature_size_padded.to_string());

    let mut rng = StdRng::seed_from_u64(0);
    let message_hash: [F; 8] = rng.random();
    let first_slot = 785555;

    let log_lifetimes = (0..n_xmss)
        .map(|_| rng.random_range(MAX_LOG_LIFETIME - 3..=MAX_LOG_LIFETIME))
        .collect::<Vec<_>>();

    let (all_public_keys, all_signatures): (Vec<_>, Vec<_>) = (0..n_xmss)
        .into_par_iter()
        .map(|i| {
            let mut rng = StdRng::seed_from_u64(i as u64);
            let log_lifetime = log_lifetimes[i];
            let signature_index = rng.random_range(first_slot..first_slot + (1 << log_lifetime));
            let xmss_secret_key = PhonyXmssSecretKey::random(&mut rng, first_slot, log_lifetime, signature_index);
            let signature = xmss_secret_key.sign(&message_hash, &mut rng);
            (xmss_secret_key.public_key, signature)
        })
        .unzip();

    let mut public_input = message_hash.to_vec();
    public_input.extend(all_public_keys.iter().flat_map(|pk| pk.merkle_root));
    public_input.extend(all_public_keys.iter().map(|pk| F::from_usize(pk.log_lifetime)));
    public_input.extend(F::zero_vec(
        all_public_keys.len().next_multiple_of(8) - all_public_keys.len(),
    ));

    let min_public_input_size = (1 << LOG_SMALLEST_DECOMPOSITION_CHUNK) - NONRESERVED_PROGRAM_INPUT_START;
    public_input.extend(F::zero_vec(min_public_input_size.saturating_sub(public_input.len())));
    public_input.insert(
        0,
        F::from_usize((public_input.len() + 8 + NONRESERVED_PROGRAM_INPUT_START).next_power_of_two()),
    );
    public_input.splice(1..1, F::zero_vec(7));

    let mut private_input = vec![];
    for (signature, pubkey) in all_signatures.iter().zip(&all_public_keys) {
        let initial_private_input_len = private_input.len();
        private_input.extend(signature.wots_signature.randomness.to_vec());
        private_input.extend(
            signature
                .wots_signature
                .chain_tips
                .iter()
                .flat_map(|digest| digest.to_vec()),
        );
        private_input.extend(signature.merkle_proof.iter().copied().flatten());
        let wots_index = signature.slot.checked_sub(pubkey.first_slot).unwrap();
        private_input.extend((0..pubkey.log_lifetime).map(|i| {
            if (wots_index >> i).is_multiple_of(2) {
                F::ONE
            } else {
                F::ZERO
            }
        }));
        let sig_size = private_input.len() - initial_private_input_len;
        private_input.extend(F::zero_vec(xmss_signature_size_padded * VECTOR_LEN - sig_size));
    }
    let bytecode = compile_program(program_str);

    // in practice we will precompute all the possible values
    // (depending on the number of recursions + the number of xmss signatures)
    // (or even better: find a linear relation)
    let no_vec_runtime_memory = execute_bytecode(
        &bytecode,
        (&public_input, &private_input),
        1 << 21,
        false,
        (&vec![], &vec![]),
    )
    .no_vec_runtime_memory;

    utils::init_tracing();

    precompute_dft_twiddles::<F>(1 << 24);

    let time = Instant::now();

    let (poseidons_16_precomputed, poseidons_24_precomputed) =
        precompute_poseidons(&all_public_keys, &all_signatures, &message_hash);

    let (proof_data, proof_size, summary) = prove_execution(
        &bytecode,
        (&public_input, &private_input),
        whir_config_builder(),
        no_vec_runtime_memory,
        false,
        (&poseidons_16_precomputed, &poseidons_24_precomputed),
    );
    let proving_time = time.elapsed();
    verify_execution(&bytecode, &public_input, proof_data, whir_config_builder()).unwrap();

    println!("{summary}");
    println!(
        "XMSS aggregation, proving time: {:.3} s ({:.1} XMSS/s), proof size: {} KiB (not optimized)",
        proving_time.as_secs_f64(),
        n_xmss as f64 / proving_time.as_secs_f64(),
        proof_size * F::bits() / (8 * 1024)
    );
}

#[instrument(skip_all)]
fn precompute_poseidons(
    xmss_pub_keys: &[XmssPublicKey],
    all_signatures: &[XmssSignature],
    message_hash: &[F; 8],
) -> (Poseidon16History, Poseidon24History) {
    assert_eq!(xmss_pub_keys.len(), all_signatures.len());
    let (poseidon_16_traces, poseidon_24_traces): (Vec<_>, Vec<_>) = xmss_pub_keys
        .par_iter()
        .zip(all_signatures.par_iter())
        .map(|(pub_key, sig)| pub_key.verify_with_poseidon_trace(message_hash, sig).unwrap())
        .unzip();
    (
        poseidon_16_traces.into_par_iter().flatten().collect(),
        poseidon_24_traces.into_par_iter().flatten().collect(),
    )
}

#[test]
fn test_xmss_aggregate() {
    let n_xmss: usize = std::env::var("NUM_XMSS_AGGREGATED")
        .unwrap_or("100".to_string())
        .parse()
        .unwrap();
    run_xmss_benchmark(n_xmss);
}
