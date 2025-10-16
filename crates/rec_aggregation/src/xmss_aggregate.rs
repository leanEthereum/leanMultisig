use std::time::{Duration, Instant};

use lean_compiler::*;
use lean_prover::whir_config_builder;
use lean_prover::{prove_execution::prove_execution, verify_execution::verify_execution};
use lean_vm::*;
use p3_field::PrimeCharacteristicRing;
use rand::{Rng, SeedableRng, rngs::StdRng};
use rayon::prelude::*;
use xmss::{PhonyXmssSecretKey, V, XmssSignature};

#[derive(Default, Debug)]
pub struct XmssBenchStats {
    pub proving_time: Duration,
    pub proof_size: usize,
    pub verified_signatures: usize,
}

pub fn run_xmss_benchmark(n_public_keys: usize) -> XmssBenchStats {
    // Public input:  message_hash | all_public_keys | bitield
    // Private input: signatures = (randomness | chain_tips | merkle_path)
    let mut program_str = r#"
    const COMPRESSION = 1;
    const PERMUTATION = 0;

    const V = 68;
    const W = 4;
    const TARGET_SUM = 114;
    const LOG_LIFETIME = LOG_LIFETIME_PLACE_HOLDER;
    const N_PUBLIC_KEYS = N_PUBLIC_KEYS_PLACE_HOLDER;
    const XMSS_SIG_SIZE = XMSS_SIG_SIZE_PLACE_HOLDER; // vectorized and padded

    fn main() {
        public_input_start_ = public_input_start;
        private_input_start = public_input_start_[0];
        message_hash = public_input_start / 8 + 1;
        all_public_keys = message_hash + 1;
        bitield = public_input_start + (2 + N_PUBLIC_KEYS) * 8;
        signatures_start = private_input_start / 8;
        for i in 0..N_PUBLIC_KEYS {
            if bitield[i] == 1 {
                xmss_public_key = all_public_keys + i;

                sig_index = counter_hint();
                signature = signatures_start + sig_index * XMSS_SIG_SIZE;

                xmss_public_key_recovered = xmss_recover_pub_key(message_hash, signature);
                assert_eq_vec(xmss_public_key, xmss_public_key_recovered);
            }
        }
        return;
    }

    fn xmss_recover_pub_key(message_hash, signature) -> 1 {
        // message_hash: vectorized pointers (of length 1)
        // signature: vectorized pointer = randomness | chain_tips | merkle_neighbours | merkle_are_left
        // return a vectorized pointer (of length 1), the hashed xmss public key
        randomness = signature; // vectorized
        chain_tips = signature + 1; // vectorized
        merkle_neighbours = chain_tips + V; // vectorized
        merkle_are_left = (merkle_neighbours + LOG_LIFETIME) * 8; // non-vectorized

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
                    dot_product(var_1, pointer_to_one_vector * 8, var_2, 1);
                    dot_product(var_3, pointer_to_one_vector * 8, var_4, 1);
                }
            }
        }

        public_key_hashed = malloc_vec(V / 2);
        poseidon24(public_key, pointer_to_zero_vector, public_key_hashed);

        for i in 1..V / 2 unroll {
            poseidon24(public_key + (2*i), public_key_hashed + (i - 1), public_key_hashed + i);
        }

        wots_pubkey_hashed = public_key_hashed + (V / 2 - 1);

        merkle_hashes = malloc_vec(LOG_LIFETIME);
        if merkle_are_left[0] == 1 {
            poseidon16(wots_pubkey_hashed, merkle_neighbours, merkle_hashes, COMPRESSION);
        } else {
            poseidon16(merkle_neighbours, wots_pubkey_hashed, merkle_hashes, COMPRESSION);
        }

        for h in 1..LOG_LIFETIME unroll {
            if merkle_are_left[h] == 1 {
                poseidon16(merkle_hashes + (h-1), merkle_neighbours + h, merkle_hashes + h, COMPRESSION);
            } else {
                poseidon16(merkle_neighbours + h, merkle_hashes + (h-1), merkle_hashes + h, COMPRESSION);
            }
        }

        return merkle_hashes + (LOG_LIFETIME - 1);
    }

    fn assert_eq_vec(x, y) inline {
        // x and y are vectorized pointer of len 1 each
        ptr_x = x * 8;
        ptr_y = y * 8;
        dot_product(ptr_x, pointer_to_one_vector * 8, ptr_y, 1);
        dot_product(ptr_x + 3, pointer_to_one_vector * 8, ptr_y + 3, 1);
        return;
    }
   "#.to_string();

    const INV_BITFIELD_DENSITY: usize = 1; // (1 / INV_BITFIELD_DENSITY) of the bits are 1 in the bitfield
    const LOG_LIFETIME: usize = 32;

    let xmss_signature_size_padded = (V + 1 + LOG_LIFETIME) + LOG_LIFETIME.div_ceil(8);
    program_str = program_str
        .replace("LOG_LIFETIME_PLACE_HOLDER", &LOG_LIFETIME.to_string())
        .replace("N_PUBLIC_KEYS_PLACE_HOLDER", &n_public_keys.to_string())
        .replace(
            "XMSS_SIG_SIZE_PLACE_HOLDER",
            &xmss_signature_size_padded.to_string(),
        );

    let bitfield = vec![true; n_public_keys];

    let mut rng = StdRng::seed_from_u64(0);
    let message_hash: [F; 8] = rng.random();

    let (all_public_keys, all_signatures): (Vec<_>, Vec<_>) = (0..n_public_keys)
        .into_par_iter()
        .map(|i| {
            let mut rng = StdRng::seed_from_u64(i as u64);
            if bitfield[i] {
                let signature_index = rng.random_range(0..1 << LOG_LIFETIME);
                let xmss_secret_key =
                    PhonyXmssSecretKey::<LOG_LIFETIME>::random(&mut rng, signature_index);
                let signature = xmss_secret_key.sign(&message_hash, &mut rng);
                (xmss_secret_key.public_key.0, Some(signature))
            } else {
                (rng.random(), None) // random pub key
            }
        })
        .unzip();
    let all_signatures: Vec<XmssSignature> = all_signatures.into_iter().flatten().collect();

    let mut public_input = message_hash.to_vec();
    public_input.extend(all_public_keys.into_iter().flatten());
    for bit in bitfield {
        public_input.push(F::from_bool(bit));
    }
    public_input.insert(
        0,
        F::from_usize((public_input.len() + 8 + PUBLIC_INPUT_START).next_power_of_two()),
    );
    public_input.splice(1..1, F::zero_vec(7));

    let mut private_input = vec![];
    for signature in all_signatures {
        private_input.extend(signature.wots_signature.randomness.to_vec());
        private_input.extend(
            signature
                .wots_signature
                .chain_tips
                .iter()
                .flat_map(|digest| digest.to_vec()),
        );
        private_input.extend(
            signature
                .merkle_proof
                .iter()
                .flat_map(|(_, neighbour)| *neighbour),
        );
        private_input.extend(
            signature
                .merkle_proof
                .iter()
                .map(|(is_left, _)| F::new(*is_left as u32)),
        );
        private_input.extend(F::zero_vec(LOG_LIFETIME.next_multiple_of(8) - LOG_LIFETIME));
    }
    let (bytecode, function_locations) = compile_program(&program_str, &public_input, &private_input);
    let time = Instant::now();

    // in practice we will precompute all the possible values
    // (depending on the number of recursions + the number of xmss signatures)
    // (or even better: find a linear relation)
    let no_vec_runtime_memory = match (n_public_keys, INV_BITFIELD_DENSITY, LOG_LIFETIME) {
        (100, 1, 32) => 148329,
        (500, 1, 32) => 741529,
        _ => unimplemented!(),
    };
    let (proof_data, proof_size) = prove_execution(
        &bytecode,
        &program_str,
        &function_locations,
        (&public_input, &private_input),
        whir_config_builder(),
        no_vec_runtime_memory,
        false,
    );
    let proving_time = time.elapsed();
    verify_execution(&bytecode, &public_input, proof_data, whir_config_builder()).unwrap();
    XmssBenchStats {
        proving_time,
        proof_size,
        verified_signatures: n_public_keys / INV_BITFIELD_DENSITY,
    }
}

#[test]
fn test_xmss_aggregate() {
    utils::init_tracing();
    use p3_field::Field;
    let n_public_keys: usize = std::env::var("NUM_XMSS_AGGREGATED")
        .unwrap_or("100".to_string())
        .parse()
        .unwrap();
    let stats = run_xmss_benchmark(n_public_keys);
    println!(
        "\nXMSS aggregation (n_signatures = {}, lifetime = 2^{})",
        stats.verified_signatures, 32
    );
    println!(
        "Proving time: {:?}, proof size: {} KiB (not optimized)",
        stats.proving_time,
        stats.proof_size * F::bits() / (8 * 1024)
    );
}
