use compiler::*;
use p3_field::PrimeCharacteristicRing;
use p3_symmetric::Permutation;
use rand::{Rng, SeedableRng, rngs::StdRng};
use utils::get_poseidon16;

use vm::*;
use xmss::{WotsSecretKey, XmssSecretKey, find_randomness_for_wots_encoding};

#[test]
fn test_verify_merkle_path() {
    let program = r#"
    const HEIGHT = 8;

    fn main() {
        public_input_start_ = public_input_start;
        private_input_start = public_input_start_[0];
        thing_to_hash = (public_input_start + 8) / 8;
        claimed_merkle_root = thing_to_hash + 1;
        are_left = (public_input_start + 8) + 16;
        neighbours = private_input_start / 8;
        merkle_root = merkle_step(0, HEIGHT, thing_to_hash, are_left, neighbours);
        print_chunk_of_8(merkle_root);
        assert_digest_eq(merkle_root,  claimed_merkle_root);
        return;
    }

    fn assert_digest_eq(a, b) {
        a_ptr = a * 8;
        b_ptr = b * 8;
        dot_product(a_ptr, pointer_to_one_vector * 8, b_ptr, 1);
        dot_product(a_ptr + 3, pointer_to_one_vector * 8, b_ptr + 3, 1);
        return;
    }

    fn merkle_step(step, height, thing_to_hash, are_left, neighbours) -> 1 {
        if step == height {
            return thing_to_hash;
        }
        is_left = are_left[0];

        hashed = malloc_vec(2);
        if is_left == 1 {
            poseidon16(thing_to_hash, neighbours, hashed);
        } else {
            poseidon16(neighbours, thing_to_hash, hashed);
        }

        next_step = step + 1;
        next_are_left = are_left + 1;
        next_neighbours = neighbours + 1;
        res = merkle_step(next_step, height, hashed, next_are_left, next_neighbours);
        return res;
    }

    fn print_chunk_of_8(arr) {
        reindexed_arr = arr * 8;
        for i in 0..8 {
            arr_i = reindexed_arr[i];
            print(arr_i);
        }
        return;
    }
   "#;

    let mut rng = StdRng::seed_from_u64(0);
    let height = 8;
    let leaf: [F; 8] = rng.random();
    let is_left = (0..height).map(|_| rng.random()).collect::<Vec<bool>>();

    let mut private_input = vec![];

    let mut to_hash = leaf;
    let poseidon16 = get_poseidon16();
    for i in 0..height {
        let neighbour: [F; 8] = rng.random();
        if is_left[i] {
            to_hash = poseidon16.permute([to_hash, neighbour].concat().try_into().unwrap())[0..8]
                .try_into()
                .unwrap();
        } else {
            to_hash = poseidon16.permute([neighbour, to_hash].concat().try_into().unwrap())[0..8]
                .try_into()
                .unwrap();
        }
        private_input.extend(neighbour);
    }

    let merkle_root = to_hash;
    dbg!(&merkle_root[0]);

    let mut public_input = leaf.to_vec();
    public_input.extend(merkle_root);
    for i in 0..height {
        if is_left[i] {
            public_input.push(F::ONE);
        } else {
            public_input.push(F::ZERO);
        }
    }
    public_input.insert(
        0,
        F::from_usize((public_input.len() + 8 + PUBLIC_INPUT_START).next_power_of_two()),
    );
    public_input.splice(1..1, F::zero_vec(7));

    compile_and_run(program, &public_input, &private_input, false);

    dbg!(&merkle_root);
}

#[test]
fn test_wots_encode() {
    // Public input: message_hash | randomness | encoding
    let program = r#"
    const V = 68;
    const W = 4;

    fn main() {
        message_hash = public_input_start / 8;
        randomness = message_hash + 1;
        expected_encoding = public_input_start + 16;
        encoding = wots_encoding(message_hash, randomness);
        for i in 0..V unroll {
            assert encoding[i] == expected_encoding[i];
        }
        return;
    }

    fn wots_encoding(message_hash, randomness) -> 1 {
        // both arguments are vectorized pointers (of length 1)
        // return a normal pointer (of length V)
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
        res = malloc(12 * 6);
        for i in 0..6 unroll {
            for j in 0..12 unroll {
                res[i * 12 + j] = bits[i * 31 + j * 2] + 2 * bits[i * 31 + j * 2 + 1];
            }
        }

        // we need to check that the (hinted) bit decomposition is valid

        for i in 0..6 unroll {
            powers_scaled_w = malloc(12);
            for j in 0..12 unroll {
                powers_scaled_w[j] = res[i*12 + j] * W**j;
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

        return res;
    }
   "#;

    let mut rng = StdRng::seed_from_u64(0);
    let message_hash: [F; 8] = rng.random();
    let (randomness, encoding) = find_randomness_for_wots_encoding(&message_hash, &mut rng);

    let mut public_input = message_hash.to_vec();
    public_input.extend(randomness.to_vec());
    public_input.extend(encoding.iter().map(|&x| F::from_u8(x)));

    compile_and_run(program, &public_input, &[], false);
}

#[test]
fn test_verify_wots_signature() {
    // Public input: wots public_key_hash | message_hash
    // Private input: signature = randomness | chain_tips
    let program = r#"

    const V = 68;
    const W = 4;

    fn main() {
        public_input_start_ = public_input_start;
        private_input_start = public_input_start_[0];
        wots_public_key_hash = (public_input_start + 8) / 8;
        message_hash = wots_public_key_hash + 1;
        signature = private_input_start / 8;
        wots_public_key_hash_recovered = wots_recover_pub_key_hashed(message_hash, signature);
        assert_digest_eq(wots_public_key_hash,  wots_public_key_hash_recovered);
        // print_chunk_of_8(wots_public_key_hash_recovered);
        return;
    }

    fn assert_digest_eq(a, b) {
        a_ptr = a * 8;
        b_ptr = b * 8;
        dot_product(a_ptr, pointer_to_one_vector * 8, b_ptr, 1);
        dot_product(a_ptr + 3, pointer_to_one_vector * 8, b_ptr + 3, 1);
        return;
    }

    fn wots_recover_pub_key_hashed(message_hash, signature) -> 1 {
        // message_hash: vectorized pointers (of length 1)
        // signature: vectorized pointer = randomness | chain_tips
        // return a vectorized pointer (of length 1), the hashed public key
        
        randomness = signature;
        chain_tips = signature + 1;

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
        for i in 0..V / 2 unroll {
            if encoding[2 * i] == 2 {
                poseidon16(pointer_to_zero_vector, chain_tips + 2 * i, public_key + 4 * i);
            } else {
                if encoding[2 * i] == 1 {
                    chain_hash_2 = malloc_vec(2);
                    poseidon16(pointer_to_zero_vector, chain_tips +  2 * i, chain_hash_2);
                    poseidon16(pointer_to_zero_vector, chain_hash_2 + 1, public_key + 4 * i);
                } else {
                    if encoding[2 * i] == 3 {
                        assert_digest_eq(chain_tips + (2 * i), (public_key + (4 * i + 1)));
                    } else {
                        // encoding[2 * i] == 0
                        chain_hash_1 = malloc_vec(2);
                        chain_hash_2 = malloc_vec(2);
                        poseidon16(pointer_to_zero_vector, chain_tips + 2 * i, chain_hash_1);
                        poseidon16(pointer_to_zero_vector, chain_hash_1 + 1, chain_hash_2);
                        poseidon16(pointer_to_zero_vector, chain_hash_2 + 1, public_key + 4 * i);
                    }
                }
            }
        }

        for i in 0..V / 2 unroll {
            if encoding[2 * i + 1] == 2 {
                poseidon16(chain_tips + 2 * i + 1, pointer_to_zero_vector, public_key + 4 * i + 2);
            } else {
                if encoding[2 * i + 1] == 1 {
                    chain_hash_2 = malloc_vec(2);
                    poseidon16(chain_tips +  2 * i + 1, pointer_to_zero_vector, chain_hash_2);
                    poseidon16(chain_hash_2, pointer_to_zero_vector, public_key + (4 * i) + 2);
                } else {
                    if encoding[2 * i + 1] == 3 {
                        assert_digest_eq(chain_tips + (2 * i + 1), (public_key + (4 * i + 2)));
                    } else {
                        // encoding[2 * i + 1] == 0
                        chain_hash_1 = malloc_vec(2);
                        chain_hash_2 = malloc_vec(2);
                        poseidon16(chain_tips + 2 * i + 1, pointer_to_zero_vector, chain_hash_1);
                        poseidon16(chain_hash_1, pointer_to_zero_vector, chain_hash_2);
                        poseidon16(chain_hash_2, pointer_to_zero_vector, public_key + 4 * i + 2);
                    }
                }
            }
        }


        public_key_hashed = malloc_vec(V / 2);
        poseidon24(public_key + 1, pointer_to_zero_vector, public_key_hashed);


        for i in 1..V / 2 unroll {
            poseidon24(public_key + (4 * i + 1), public_key_hashed + (i - 1), public_key_hashed + i);
        }

        return public_key_hashed + (V / 2 - 1);
    }

    fn print_chunk_of_8(arr) {
        reindexed_arr = arr * 8;
        for i in 0..8 {
            arr_i = reindexed_arr[i];
            print(arr_i);
        }
        return;
    }

   "#;

    let mut rng = StdRng::seed_from_u64(0);
    let message_hash: [F; 8] = rng.random();
    let wots_secret_key = WotsSecretKey::random(&mut rng);
    let signature = wots_secret_key.sign(&message_hash, &mut rng);
    let public_key_hashed = wots_secret_key.public_key().hash();
    // dbg!(public_key_hashed);

    let mut public_input = public_key_hashed.to_vec();
    public_input.extend(message_hash);

    let mut private_input = signature.randomness.to_vec();
    private_input.extend(
        signature
            .chain_tips
            .iter()
            .flat_map(|digest| digest.to_vec()),
    );

    public_input.insert(
        0,
        F::from_usize((public_input.len() + 8 + PUBLIC_INPUT_START).next_power_of_two()),
    );
    public_input.splice(1..1, F::zero_vec(7));

    compile_and_run(program, &public_input, &private_input, false);
}

#[test]
fn test_verify_xmss_signature() {
    // Public input: public_key_hash | message_hash
    // Private input: signature = randomness | chain_tips | merkle_path
    let mut program = r#"

    const V = 68;
    const W = 4;
    const LOG_LIFETIME = LOG_LIFETIME_PLACE_HOLDER;

    fn main() {
        public_input_start_ = public_input_start;
        private_input_start = public_input_start_[0];
        xmss_public_key = (public_input_start + 8) / 8;
        message_hash = xmss_public_key + 1;
        signature = private_input_start / 8;
        xmss_public_key_recovered = xmss_recover_pub_key(message_hash, signature);
        // print_chunk_of_8(xmss_public_key_recovered);
        assert_digest_eq(xmss_public_key, xmss_public_key_recovered);
        return;
    }

    fn assert_digest_eq(a, b) {
        a_ptr = a * 8;
        b_ptr = b * 8;
        dot_product(a_ptr, pointer_to_one_vector * 8, b_ptr, 1);
        dot_product(a_ptr + 3, pointer_to_one_vector * 8, b_ptr + 3, 1);
        return;
    }

    fn xmss_recover_pub_key(message_hash, signature) -> 1 {
        // message_hash: vectorized pointers (of length 1)
        // signature: vectorized pointer = randomness | chain_tips | merkle_neighbours | merkle_are_left
        // return a vectorized pointer (of length 1), the hashed public key

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
        for i in 0..V / 2 unroll {
            if encoding[2 * i] == 2 {
                poseidon16(pointer_to_zero_vector, chain_tips + 2 * i, public_key + 4 * i);
            } else {
                if encoding[2 * i] == 1 {
                    chain_hash_2 = malloc_vec(2);
                    poseidon16(pointer_to_zero_vector, chain_tips +  2 * i, chain_hash_2);
                    poseidon16(pointer_to_zero_vector, chain_hash_2 + 1, public_key + 4 * i);
                } else {
                    if encoding[2 * i] == 3 {
                        // trick: use the DOT_PRODUCT precompile to assert an equality between 2 chunks of 8 field elements
                        assert_digest_eq(chain_tips + (2 * i), (public_key + (4 * i + 1)));
                    } else {
                        // encoding[2 * i] == 0
                        chain_hash_1 = malloc_vec(2);
                        chain_hash_2 = malloc_vec(2);
                        poseidon16(pointer_to_zero_vector, chain_tips + 2 * i, chain_hash_1);
                        poseidon16(pointer_to_zero_vector, chain_hash_1 + 1, chain_hash_2);
                        poseidon16(pointer_to_zero_vector, chain_hash_2 + 1, public_key + 4 * i);
                    }
                }
            }
        }

        for i in 0..V / 2 unroll {
            if encoding[2 * i + 1] == 2 {
                poseidon16(chain_tips + 2 * i + 1, pointer_to_zero_vector, public_key + 4 * i + 2);
            } else {
                if encoding[2 * i + 1] == 1 {
                    chain_hash_2 = malloc_vec(2);
                    poseidon16(chain_tips +  2 * i + 1, pointer_to_zero_vector, chain_hash_2);
                    poseidon16(chain_hash_2, pointer_to_zero_vector, public_key + (4 * i) + 2);
                } else {
                    if encoding[2 * i + 1] == 3 {
                        // trick: use the DOT_PRODUCT precompile to assert an equality between 2 chunks of 8 field elements
                        assert_digest_eq(chain_tips + (2 * i + 1), (public_key + (4 * i + 2)));
                    } else {
                        // encoding[2 * i + 1] == 0
                        chain_hash_1 = malloc_vec(2);
                        chain_hash_2 = malloc_vec(2);
                        poseidon16(chain_tips + 2 * i + 1, pointer_to_zero_vector, chain_hash_1);
                        poseidon16(chain_hash_1, pointer_to_zero_vector, chain_hash_2);
                        poseidon16(chain_hash_2, pointer_to_zero_vector, public_key + 4 * i + 2);
                    }
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

    fn print_chunk_of_8(arr) {
        reindexed_arr = arr * 8;
        for i in 0..8 {
            arr_i = reindexed_arr[i];
            print(arr_i);
        }
        return;
    }

   "#.to_string();

    const LOG_LIFETIME: usize = 5;

    program = program.replace("LOG_LIFETIME_PLACE_HOLDER", &LOG_LIFETIME.to_string());

    let mut rng = StdRng::seed_from_u64(0);
    let message_hash: [F; 8] = rng.random();
    let xmss_secret_key = XmssSecretKey::<LOG_LIFETIME>::random(&mut rng);
    let signature = xmss_secret_key.sign(&message_hash, 2, &mut rng);
    // dbg!(public_key_hashed);

    let mut public_input = xmss_secret_key.public_key().0.to_vec();
    public_input.extend(message_hash);

    let mut private_input = signature.wots_signature.randomness.to_vec();
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
    public_input.insert(
        0,
        F::from_usize((public_input.len() + 8 + PUBLIC_INPUT_START).next_power_of_two()),
    );
    public_input.splice(1..1, F::zero_vec(7));

    compile_and_run(&program, &public_input, &private_input, false);
}
