use std::{env, time::Instant};

use compiler::*;
use p3_field::PrimeCharacteristicRing;
use rand::{Rng, SeedableRng, rngs::StdRng};
use rayon::prelude::*;

use vm::*;
use xmss::{PhonyXmssSecretKey, V, XmssSignature};
use zk_vm::{
    build_batch_pcs, prove_execution::prove_execution, verify_execution::verify_execution,
};

#[test]
fn test_xmss_aggregate() {
    // Public input:  message_hash | all_public_keys | bitield
    // Private input: signatures = (randomness | chain_tips | merkle_path)
    let mut program_str = r#"

    const V = 68;
    const W = 4;
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

        compressed = malloc_vec(2);
        poseidon16(message_hash, randomness, compressed);
        compressed_ptr = compressed * 8;
        bits = decompose_bits(compressed_ptr[0], compressed_ptr[1], compressed_ptr[2], compressed_ptr[3], compressed_ptr[4], compressed_ptr[5]);
        flipped_bits = malloc(186);
        for i in 0..186 unroll {
            flipped_bits[i] = 1 - bits[i];
        }
        zero = 0;
        for i in 0..186 unroll {
            zero = flipped_bits[i] * bits[i]; // TODO remove the use of auxiliary var (currently it generates 2 instructions instead of 1)
        }
        encoding = malloc(12 * 6);
        for i in 0..6 unroll {
            for j in 0..12 unroll {
                encoding[i * 12 + j] = bits[i * 31 + j * 2] + 2 * bits[i * 31 + j * 2 + 1];
            }
        }

        // we need to check that the (hinted) bit decomposition is valid

        for i in 0..6 unroll {
            powers_scaled_w = malloc(12);
            for j in 0..12 unroll {
                powers_scaled_w[j] = encoding[i*12 + j] * W**j;
            }
            powers_scaled_sum_w = malloc(11);
            powers_scaled_sum_w[0] = powers_scaled_w[0] + powers_scaled_w[1];
            for j in 1..11 unroll {
                powers_scaled_sum_w[j] = powers_scaled_sum_w[j - 1] + powers_scaled_w[j + 1];
            }

            powers_scaled_2 = malloc(7);
            for j in 0..7 unroll {
                powers_scaled_2[j] = bits[31 * i + 24 + j] * 2**(24 + j);
            }
            powers_scaled_sum_2 = malloc(6);
            powers_scaled_sum_2[0] = powers_scaled_2[0] + powers_scaled_2[1];
            for j in 1..6 unroll {
                powers_scaled_sum_2[j] = powers_scaled_sum_2[j - 1] + powers_scaled_2[j + 1];
            }

            assert powers_scaled_sum_w[10] + powers_scaled_sum_2[5] == compressed_ptr[i];
        }

        public_key = malloc_vec(V * 2);

        chain_tips_ptr = 8 * chain_tips;
        public_key_ptr = 8 * public_key;

        for i in 0..V / 2 unroll {
            match encoding[2 * i] {
                0 => {
                    chain_hash_1 = malloc_vec(2);
                    chain_hash_2 = malloc_vec(2);
                    poseidon16(pointer_to_zero_vector, chain_tips + 2 * i, chain_hash_1);
                    poseidon16(pointer_to_zero_vector, chain_hash_1 + 1, chain_hash_2);
                    poseidon16(pointer_to_zero_vector, chain_hash_2 + 1, public_key + 4 * i);
                }
                1 => {
                    chain_hash_2 = malloc_vec(2);
                    poseidon16(pointer_to_zero_vector, chain_tips +  2 * i, chain_hash_2);
                    poseidon16(pointer_to_zero_vector, chain_hash_2 + 1, public_key + 4 * i);
                }
                2 => {
                    poseidon16(pointer_to_zero_vector, chain_tips + 2 * i, public_key + 4 * i);
                }
                3 => {
                    assert_eq_vec_deref(chain_tips_ptr + ((2 * i) * 8), public_key_ptr + ((4 * i + 1) * 8));
                }
            }
        }

        for i in 0..V / 2 unroll {
            match encoding[2 * i + 1] {
                0 => {
                    chain_hash_1 = malloc_vec(2);
                    chain_hash_2 = malloc_vec(2);
                    poseidon16(chain_tips + 2 * i + 1, pointer_to_zero_vector, chain_hash_1);
                    poseidon16(chain_hash_1, pointer_to_zero_vector, chain_hash_2);
                    poseidon16(chain_hash_2, pointer_to_zero_vector, public_key + 4 * i + 2);
                }
                1 => {
                    chain_hash_2 = malloc_vec(2);
                    poseidon16(chain_tips +  2 * i + 1, pointer_to_zero_vector, chain_hash_2);
                    poseidon16(chain_hash_2, pointer_to_zero_vector, public_key + (4 * i) + 2);
                }
                2 => {
                    poseidon16(chain_tips + 2 * i + 1, pointer_to_zero_vector, public_key + 4 * i + 2);
                }
                3 => {
                    assert_eq_vec_deref(chain_tips_ptr + ((2 * i + 1) * 8), public_key_ptr + ((4 * i + 2) * 8));
                }
            }
        }


        public_key_hashed = malloc_vec(V / 2);
        poseidon24(public_key + 1, pointer_to_zero_vector, public_key_hashed);


        for i in 1..V / 2 unroll {
            poseidon24(public_key + (4 * i + 1), public_key_hashed + (i - 1), public_key_hashed + i);
        }

        wots_pubkey_hashed = public_key_hashed + (V / 2 - 1);

        merkle_hashes = malloc_vec(LOG_LIFETIME * 2);
        if merkle_are_left[0] == 1 {
            poseidon16(wots_pubkey_hashed, merkle_neighbours, merkle_hashes);
        } else {
            poseidon16(merkle_neighbours, wots_pubkey_hashed, merkle_hashes);
        }

        for h in 1..LOG_LIFETIME unroll {
            if merkle_are_left[h] == 1 {
                poseidon16(merkle_hashes + (2 * (h-1)), merkle_neighbours + h, merkle_hashes + 2 * h);
            } else {
                poseidon16(merkle_neighbours + h, merkle_hashes + (2 * (h-1)), merkle_hashes + 2 * h);
            }
        }

        return merkle_hashes + (LOG_LIFETIME * 2 - 2);
    }

    fn assert_eq_vec(x, y) inline {
        // x and y are vectorized pointer of len 1 each
        ptr_x = x * 8;
        ptr_y = y * 8;
        dot_product(ptr_x, pointer_to_one_vector * 8, ptr_y, 1);
        dot_product(ptr_x + 3, pointer_to_one_vector * 8, ptr_y + 3, 1);
        return;
    }

    fn assert_eq_vec_deref(x, y) inline {
        // x and y are normal pointer of len 8 each
        dot_product(x, pointer_to_one_vector * 8, y, 1);
        dot_product(x + 3, pointer_to_one_vector * 8, y + 3, 1);
        return;
    }
   "#.to_string();

    const LOG_LIFETIME: usize = 32;
    const INV_BITFIELD_DENSITY: usize = 1; // (1 / INV_BITFIELD_DENSITY) of the bits are 1 in the bitfield

    let n_public_keys: usize = env::var("NUM_XMSS_AGGREGATED")
        .unwrap_or("100".to_string())
        .parse()
        .unwrap();

    let xmss_signature_size_padded = (V + 1 + LOG_LIFETIME) + LOG_LIFETIME.div_ceil(8);
    program_str = program_str
        .replace("LOG_LIFETIME_PLACE_HOLDER", &LOG_LIFETIME.to_string())
        .replace("N_PUBLIC_KEYS_PLACE_HOLDER", &n_public_keys.to_string())
        .replace(
            "XMSS_SIG_SIZE_PLACE_HOLDER",
            &xmss_signature_size_padded.to_string(),
        );

    let bitfield = (0..n_public_keys)
        .map(|i| i % INV_BITFIELD_DENSITY == 0)
        .collect::<Vec<_>>();

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
    if env::var("PROVE_XMSS_AGGREGATED").unwrap_or("true".to_string()) == "true" {
        utils::init_tracing();
        let (bytecode, function_locations) = compile_program(&program_str);
        let batch_pcs = build_batch_pcs();
        let time = Instant::now();
        let proof_data = prove_execution(
            &bytecode,
            &program_str,
            &function_locations,
            &public_input,
            &private_input,
            &batch_pcs,
            false,
        );
        let proving_time = time.elapsed();
        verify_execution(&bytecode, &public_input, proof_data, &batch_pcs).unwrap();
        println!(
            "XMSS aggregation (n_signatures = {}, lifetime = 2^{})",
            n_public_keys / INV_BITFIELD_DENSITY,
            LOG_LIFETIME
        );
        println!("Proving time: {proving_time:?}");
    } else {
        compile_and_run(&program_str, &public_input, &private_input, false);
    }
}
