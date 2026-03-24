from snark_lib import *
from utils import *

V = V_PLACEHOLDER
W = W_PLACEHOLDER
CHAIN_LENGTH = 2**W
TARGET_SUM = TARGET_SUM_PLACEHOLDER
LOG_LIFETIME = LOG_LIFETIME_PLACEHOLDER
MESSAGE_LEN = MESSAGE_LEN_PLACEHOLDER
RANDOMNESS_LEN = RANDOMNESS_LEN_PLACEHOLDER
PUBLIC_PARAM_LEN = PUBLIC_PARAM_LEN_PLACEHOLDER
TWEAK_LEN = TWEAK_LEN_PLACEHOLDER
PUBKEY_SIZE = DIGEST_LEN + PUBLIC_PARAM_LEN
SIG_SIZE = RANDOMNESS_LEN + (V + LOG_LIFETIME) * DIGEST_LEN
MERKLE_LEVELS_PER_CHUNK = MERKLE_LEVELS_PER_CHUNK_PLACEHOLDER
N_MERKLE_CHUNKS = 8  # LOG_LIFETIME // MERKLE_LEVELS_PER_CHUNK = 32 // 4
WOTS_PUBKET_SPONGE_DOMAIN_SEP = WOTS_PUBKET_SPONGE_DOMAIN_SEP_PLACEHOLDER

POSEIDON24_CAP = 9
POSEIDON24_RATE = 15
CHUNKS_PER_FE = 24 / W  # 8
NUM_ENCODING_FE = div_ceil(V, CHUNKS_PER_FE)  # ceil(V/8)
Q = 127  # Rejection parameter: p = Q * CHAIN_LENGTH^CHUNKS_PER_FE + 1 = 127 * 8^8 + 1

# All tweaks layout: encoding_tweak(2) + chain_tweaks(V*CHAIN_LENGTH*2) + leaf_tweak(2) + merkle_tweaks(LOG_LIFETIME*2)
N_ALL_TWEAKS = TWEAK_LEN + V * CHAIN_LENGTH * TWEAK_LEN + TWEAK_LEN + LOG_LIFETIME * TWEAK_LEN
CHAIN_TWEAKS_OFFSET = TWEAK_LEN
LEAF_TWEAK_OFFSET = TWEAK_LEN + V * CHAIN_LENGTH * TWEAK_LEN
MERKLE_TWEAKS_OFFSET = TWEAK_LEN + V * CHAIN_LENGTH * TWEAK_LEN + TWEAK_LEN


@inline
def xmss_verify(merkle_root, public_param, message, signature, all_tweaks, merkle_chunks):
    # signature layout: randomness | chain_tips | merkle_path
    randomness = signature
    chain_starts = signature + RANDOMNESS_LEN
    merkle_path = chain_starts + V * DIGEST_LEN

    # Tweak pointers (all pre-computed in public input)
    encoding_tweak = all_tweaks
    chain_tweaks = all_tweaks + CHAIN_TWEAKS_OFFSET
    leaf_tweak = all_tweaks + LEAF_TWEAK_OFFSET
    merkle_tweaks = all_tweaks + MERKLE_TWEAKS_OFFSET

    # 1) Encode: poseidon24_compress_0_9(message(9) || pp(5) || slot(2) || randomness(7)  || 0)
    enc_rate = Array(15)
    copy_5(public_param, enc_rate)
    enc_rate[5] = encoding_tweak[0]
    enc_rate[6] = encoding_tweak[1]
    copy_7(randomness, enc_rate + 7)
    enc_rate[14] = 0

    encoding_fe = Array(POSEIDON24_CAP)
    poseidon24_compress_0_9(message, enc_rate, encoding_fe)

    # 2) Decompose encoding_fe into chain indices (only first NUM_ENCODING_FE elements)
    encoding = Array(NUM_ENCODING_FE * CHUNKS_PER_FE)
    remaining = Array(NUM_ENCODING_FE)
    hint_decompose_bits_xmss(encoding, remaining, encoding_fe, NUM_ENCODING_FE, W)

    for i in unroll(0, NUM_ENCODING_FE):
        for j in unroll(0, CHUNKS_PER_FE):
            assert encoding[i * CHUNKS_PER_FE + j] < CHAIN_LENGTH
        assert remaining[i] < Q
        partial_sum: Mut = remaining[i]
        for j in unroll(0, CHUNKS_PER_FE):
            partial_sum += encoding[i * CHUNKS_PER_FE + j] * (Q * CHAIN_LENGTH ** j)
        assert partial_sum == encoding_fe[i]

    # 3) Chain hashing with Poseidon16 + pre-computed tweaks
    target_sum: Mut = 0
    wots_public_key = Array(V * DIGEST_LEN)

    for i in unroll(0, V):
        chain_start = chain_starts + i * DIGEST_LEN
        chain_end = wots_public_key + i * DIGEST_LEN
        enc_val_ptr = encoding + i
        chain_sum_ptr = Array(1)
        match_range(
            enc_val_ptr[0], range(0, CHAIN_LENGTH),
            lambda n: chain_hash(chain_start, n, chain_end, chain_sum_ptr, public_param, chain_tweaks, i)
        )
        target_sum += chain_sum_ptr[0]

    assert target_sum == TARGET_SUM

    # 4) WOTS PK hash with Poseidon24 sponge (parameter + leaf_tweak prefix)
    wots_pk_hashed = wots_pk_hash_p24(wots_public_key, public_param, leaf_tweak)

    # 5) Merkle verify with Poseidon24 + pre-computed tweaks
    xmss_merkle_verify_p24(wots_pk_hashed, merkle_path, merkle_chunks, merkle_root, public_param, merkle_tweaks)

    return


@inline
def make_chain_right(public_param, chain_tweaks, chain_index, step):
    right = Array(DIGEST_LEN)
    tweak_idx = (chain_index * CHAIN_LENGTH + step) * TWEAK_LEN
    copy_5(public_param, right)
    right[5] = chain_tweaks[tweak_idx]
    right[6] = chain_tweaks[tweak_idx + 1]
    right[7] = 0
    return right


@inline
def chain_hash(input_ptr, n, output_ptr, chain_sum_ptr, public_param, chain_tweaks, chain_index):
    num_hashes = (CHAIN_LENGTH - 1) - n
    start_step = n + 1

    if num_hashes == 0:
        copy_8(input_ptr, output_ptr)
    elif num_hashes == 1:
        right = make_chain_right(public_param, chain_tweaks, chain_index, start_step)
        poseidon16_compress(input_ptr, right, output_ptr)
    else:
        states = Array((num_hashes - 1) * DIGEST_LEN)
        right0 = make_chain_right(public_param, chain_tweaks, chain_index, start_step)
        poseidon16_compress(input_ptr, right0, states)
        for j in unroll(1, num_hashes - 1):
            right_j = make_chain_right(public_param, chain_tweaks, chain_index, start_step + j)
            poseidon16_compress(states + (j - 1) * DIGEST_LEN, right_j, states + j * DIGEST_LEN)
        right_last = make_chain_right(public_param, chain_tweaks, chain_index, start_step + num_hashes - 1)
        poseidon16_compress(states + (num_hashes - 2) * DIGEST_LEN, right_last, output_ptr)

    chain_sum_ptr[0] = n
    return


@inline
def wots_pk_hash_p24(wots_pk, public_param, leaf_tweak):
    # Sponge input: parameter(5) | leaf_tweak(2) | chain_ends(V*8) = 375 elements
    # 375 / 15 = 25 exact chunks, no remainder
    PREFIX_LEN = PUBLIC_PARAM_LEN + TWEAK_LEN  # 7
    capacity: Mut = Array(POSEIDON24_CAP)
    for i in unroll(0, POSEIDON24_CAP):
        capacity[i] = WOTS_PUBKET_SPONGE_DOMAIN_SEP[i]
    # First chunk: parameter(5) | leaf_tweak(2) | wots_pk[0..8]
    first_rate = Array(POSEIDON24_RATE)
    copy_5(public_param, first_rate)
    first_rate[5] = leaf_tweak[0]
    first_rate[6] = leaf_tweak[1]
    copy_8(wots_pk, first_rate + PREFIX_LEN)
    new_capacity = Array(POSEIDON24_CAP)
    poseidon24_permute_0_9(capacity, first_rate, new_capacity)
    capacity = new_capacity
    # Remaining data: wots_pk[8..] = V*DIGEST_LEN - 8 elements
    WOTS_PK_OFFSET = POSEIDON24_RATE - PREFIX_LEN  # 8
    REMAINING = V * DIGEST_LEN - WOTS_PK_OFFSET
    REMAINDER = REMAINING % POSEIDON24_RATE
    N_FULL_STEPS = div_floor(REMAINING, POSEIDON24_RATE)
    for step in unroll(0, N_FULL_STEPS):
        src = wots_pk + WOTS_PK_OFFSET + step * POSEIDON24_RATE
        new_capacity = Array(POSEIDON24_CAP)
        if step == N_FULL_STEPS - 1:
            if REMAINDER == 0:
                poseidon24_permute_9_18(capacity, src, new_capacity)
            else:
                poseidon24_permute_0_9(capacity, src, new_capacity)
        else:
            poseidon24_permute_0_9(capacity, src, new_capacity)
        capacity = new_capacity
    if REMAINDER != 0:
        src = wots_pk + WOTS_PK_OFFSET + N_FULL_STEPS * POSEIDON24_RATE
        rate = Array(POSEIDON24_RATE)
        for i in unroll(0, REMAINDER):
            rate[i] = src[i]
        for i in unroll(REMAINDER, POSEIDON24_RATE):
            rate[i] = 0
        new_capacity = Array(POSEIDON24_CAP)
        poseidon24_permute_9_18(capacity, rate, new_capacity)
        capacity = new_capacity
    return capacity


@inline
def xmss_merkle_verify_p24(leaf_digest, merkle_path, merkle_chunks, expected_root, public_param, merkle_tweaks):
    states = Array((N_MERKLE_CHUNKS - 1) * DIGEST_LEN)

    match_range(merkle_chunks[0], range(0, 16), lambda b:
        do_4_merkle_levels_p24(b, leaf_digest, merkle_path, states, public_param, merkle_tweaks, 0))

    for j in unroll(1, N_MERKLE_CHUNKS - 1):
        match_range(merkle_chunks[j], range(0, 16), lambda b:
            do_4_merkle_levels_p24(
                b, states + (j - 1) * DIGEST_LEN,
                merkle_path + j * MERKLE_LEVELS_PER_CHUNK * DIGEST_LEN,
                states + j * DIGEST_LEN,
                public_param, merkle_tweaks, j * MERKLE_LEVELS_PER_CHUNK))

    match_range(merkle_chunks[N_MERKLE_CHUNKS - 1], range(0, 16), lambda b:
        do_4_merkle_levels_p24(
            b, states + (N_MERKLE_CHUNKS - 2) * DIGEST_LEN,
            merkle_path + (N_MERKLE_CHUNKS - 1) * MERKLE_LEVELS_PER_CHUNK * DIGEST_LEN,
            expected_root,
            public_param, merkle_tweaks, (N_MERKLE_CHUNKS - 1) * MERKLE_LEVELS_PER_CHUNK))
    return


@inline
def do_4_merkle_levels_p24(b, state_in, path_chunk, state_out, public_param, merkle_tweaks, base_level):
    b0 = b % 2
    r1 = (b - b0) / 2
    b1 = r1 % 2
    r2 = (r1 - b1) / 2
    b2 = r2 % 2
    r3 = (r2 - b2) / 2
    b3 = r3 % 2

    temps = Array(3 * DIGEST_LEN)

    merkle_p24_one_level(b0, state_in, path_chunk, temps, public_param, merkle_tweaks, base_level)
    merkle_p24_one_level(b1, temps, path_chunk + DIGEST_LEN, temps + DIGEST_LEN, public_param, merkle_tweaks, base_level + 1)
    merkle_p24_one_level(b2, temps + DIGEST_LEN, path_chunk + 2 * DIGEST_LEN, temps + 2 * DIGEST_LEN, public_param, merkle_tweaks, base_level + 2)
    merkle_p24_one_level(b3, temps + 2 * DIGEST_LEN, path_chunk + 3 * DIGEST_LEN, state_out, public_param, merkle_tweaks, base_level + 3)
    return


@inline
def merkle_p24_one_level(is_left_bit, current, neighbour, output, public_param, merkle_tweaks, child_level):
    tweak_ptr = merkle_tweaks + child_level * TWEAK_LEN

    input_buf = Array(24)
    copy_5(public_param, input_buf)
    input_buf[5] = tweak_ptr[0]
    input_buf[6] = tweak_ptr[1]
    if is_left_bit == 0:
        copy_8(neighbour, input_buf + 7)
        copy_8(current, input_buf + 15)
    else:
        copy_8(current, input_buf + 7)
        copy_8(neighbour, input_buf + 15)
    input_buf[23] = 0

    merkle_output = Array(POSEIDON24_CAP)
    poseidon24_compress_0_9(input_buf, input_buf + 9, merkle_output)
    for k in unroll(0, DIGEST_LEN):
        output[k] = merkle_output[k]
    return


@inline
def copy_7(x, y):
    dot_product_ee(x, ONE_EF_PTR, y)
    dot_product_ee(x + (7 - DIM), ONE_EF_PTR, y + (7 - DIM))
    return
