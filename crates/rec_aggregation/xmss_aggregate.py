from snark_lib import *
from utils import *

V = V_PLACEHOLDER
V_GRINDING = V_GRINDING_PLACEHOLDER
W = W_PLACEHOLDER
CHAIN_LENGTH = 2 ** W
TARGET_SUM = TARGET_SUM_PLACEHOLDER
LOG_LIFETIME = LOG_LIFETIME_PLACEHOLDER
MESSAGE_LEN = MESSAGE_LEN_PLACEHOLDER
RANDOMNESS_LEN = RANDOMNESS_LEN_PLACEHOLDER
SIG_SIZE = RANDOMNESS_LEN + (V + LOG_LIFETIME) * DIGEST_LEN
NUM_ENCODING_FE = div_ceil((V + V_GRINDING), (24 / W)) # 24 should be divisible by W (works for W=2,3,4)
MERKLE_LEVELS_PER_CHUNK = MERKLE_LEVELS_PER_CHUNK_PLACEHOLDER
N_MERKLE_CHUNKS = LOG_LIFETIME / MERKLE_LEVELS_PER_CHUNK


@inline
def xmss_verify(merkle_root, message, signature, slot_lo, slot_hi, merkle_chunks):
    # signature: randomness | chain_tips | merkle_path
    # return the hashed xmss public key
    randomness = signature
    chain_starts = signature + RANDOMNESS_LEN
    merkle_path = chain_starts + V * DIGEST_LEN

    # 1) We encode message_hash + randomness into the layer of the hypercube with target sum = TARGET_SUM

    a_input_right = Array(DIGEST_LEN)
    b_input = Array(DIGEST_LEN * 2)
    a_input_right[0] = message[DIGEST_LEN]
    copy_7(randomness, a_input_right + 1)
    poseidon16(message, a_input_right, b_input)
    b_input[DIGEST_LEN] = slot_lo
    b_input[DIGEST_LEN + 1] = slot_hi
    copy_6(merkle_root, b_input + DIGEST_LEN + 2)
    encoding_fe = Array(DIGEST_LEN)
    poseidon16(b_input, b_input + DIGEST_LEN, encoding_fe)

    encoding = Array(NUM_ENCODING_FE * 24 / (2 * W))
    remaining = Array(NUM_ENCODING_FE)

    hint_decompose_bits_xmss(
        encoding,
        remaining,
        encoding_fe,
        NUM_ENCODING_FE,
        2 * W
    )

    # check that the decomposition is correct
    for i in unroll(0, NUM_ENCODING_FE):
        for j in unroll(0, 24 / (2 * W)):
            assert encoding[i * (24 / (2 * W)) + j] < CHAIN_LENGTH**2

        assert remaining[i] < 2**7 - 1 # ensures uniformity + prevent overflow

        partial_sum: Mut = remaining[i] * 2**24
        for j in unroll(0, 24/(2*W)):
            partial_sum += encoding[i * (24 / (2 * W)) + j] * (CHAIN_LENGTH ** 2) ** j
        assert partial_sum == encoding_fe[i]

    # grinding
    debug_assert(V_GRINDING % 2 == 0)
    debug_assert(V % 2 == 0)
    for i in unroll(V / 2, (V + V_GRINDING) / 2):
        assert encoding[i] == CHAIN_LENGTH**2 - 1

    target_sum: Mut = 0
    
    wots_public_key = Array(V * DIGEST_LEN)

    local_zero_buff = Array(DIGEST_LEN)
    set_to_8_zeros(local_zero_buff)

    for i in unroll(0, V / 2):
        # num_hashes = (CHAIN_LENGTH - 1) - encoding[i]
        chain_start = chain_starts + i * (DIGEST_LEN * 2)
        chain_end = wots_public_key + i * (DIGEST_LEN * 2)
        pair_chain_length_sum_ptr = Array(1)
        match_range(encoding[i], range(0, CHAIN_LENGTH**2), lambda n: chain_hash(chain_start, n, chain_end, pair_chain_length_sum_ptr, local_zero_buff))
        target_sum += pair_chain_length_sum_ptr[0]

    assert target_sum == TARGET_SUM

    wots_pubkey_hashed = slice_hash(wots_public_key, V)

    xmss_merkle_verify(wots_pubkey_hashed, merkle_path, merkle_chunks, merkle_root)

    return


@inline
def chain_hash(input_left, n, output_left, pair_chain_length_sum_ptr, local_zero_buff):
    debug_assert(n < CHAIN_LENGTH**2)

    raw_left = n % CHAIN_LENGTH
    raw_right = (n - raw_left) / CHAIN_LENGTH

    n_left = (CHAIN_LENGTH - 1) - raw_left
    if n_left == 0:
        copy_8(input_left, output_left)
    elif n_left == 1:
        poseidon16(input_left, local_zero_buff, output_left)
    else:
        states_left = Array((n_left-1) * DIGEST_LEN)
        poseidon16(input_left, local_zero_buff, states_left)
        for i in unroll(1, n_left-1):
            poseidon16(states_left + (i - 1) * DIGEST_LEN, local_zero_buff, states_left + i * DIGEST_LEN)
        poseidon16(states_left + (n_left - 2) * DIGEST_LEN, local_zero_buff, output_left)

    n_right = (CHAIN_LENGTH - 1) - raw_right
    debug_assert(raw_right < CHAIN_LENGTH)
    input_right = input_left + DIGEST_LEN
    output_right = output_left + DIGEST_LEN
    if n_right == 0:
        copy_8(input_right, output_right)
    elif n_right == 1:
        poseidon16(input_right, local_zero_buff, output_right)
    else:
        states_right = Array((n_right-1) * DIGEST_LEN)
        poseidon16(input_right, local_zero_buff, states_right)
        for i in unroll(1, n_right-1):
            poseidon16(states_right + (i - 1) * DIGEST_LEN, local_zero_buff, states_right + i * DIGEST_LEN)
        poseidon16(states_right + (n_right - 2) * DIGEST_LEN, local_zero_buff, output_right)

    pair_chain_length_sum_ptr[0] = raw_left + raw_right

    return


@inline
def do_4_merkle_levels(b, state_in, path_chunk, state_out):
    # Extract bits of b (compile-time; each division is exact so field div == integer div)
    b0 = b % 2
    r1 = (b - b0) / 2
    b1 = r1 % 2
    r2 = (r1 - b1) / 2
    b2 = r2 % 2
    r3 = (r2 - b2) / 2
    b3 = r3 % 2

    temps = Array(3 * DIGEST_LEN)

    # Level 0: state_in -> temps
    if b0 == 0:
        poseidon16(path_chunk, state_in, temps)
    else:
        poseidon16(state_in, path_chunk, temps)


    # Level 1
    if b1 == 0:
        poseidon16(path_chunk + 1 * DIGEST_LEN, temps, temps + DIGEST_LEN)
    else:
        poseidon16(temps, path_chunk + 1 * DIGEST_LEN, temps + DIGEST_LEN)

    # Level 2
    if b2 == 0:
        poseidon16(path_chunk + 2 * DIGEST_LEN, temps + DIGEST_LEN, temps + 2 * DIGEST_LEN)
    else:
        poseidon16(temps + DIGEST_LEN, path_chunk + 2 * DIGEST_LEN, temps + 2 * DIGEST_LEN)

    # Level 3: -> state_out
    if b3 == 0:
        poseidon16(path_chunk + 3 * DIGEST_LEN, temps + 2 * DIGEST_LEN, state_out)
    else:
        poseidon16(temps + 2 * DIGEST_LEN, path_chunk + 3 * DIGEST_LEN, state_out)
    return


@inline
def xmss_merkle_verify(leaf_digest, merkle_path, merkle_chunks, expected_root):
    states = Array((N_MERKLE_CHUNKS - 1) * DIGEST_LEN)

    # First chunk: leaf_digest -> states
    match_range(merkle_chunks[0], range(0, 16), lambda b: do_4_merkle_levels(b, leaf_digest, merkle_path, states))

    # Middle chunks
    for j in unroll(1, N_MERKLE_CHUNKS - 1):
        match_range(merkle_chunks[j], range(0, 16), lambda b: do_4_merkle_levels(b, states + (j - 1) * DIGEST_LEN, merkle_path + j * MERKLE_LEVELS_PER_CHUNK * DIGEST_LEN, states + j * DIGEST_LEN))

    # Last chunk: -> expected_root
    match_range(merkle_chunks[N_MERKLE_CHUNKS - 1], range(0, 16), lambda b: do_4_merkle_levels(b, states + (N_MERKLE_CHUNKS - 2) * DIGEST_LEN, merkle_path + (N_MERKLE_CHUNKS - 1) * MERKLE_LEVELS_PER_CHUNK * DIGEST_LEN, expected_root))
    return


@inline
def copy_7(x, y):
    dot_product_ee(x, ONE_EF_PTR, y)
    dot_product_ee(x + (7-DIM), ONE_EF_PTR, y + (7-DIM))
    return


@inline
def copy_6(x, y):
    dot_product_ee(x, ONE_EF_PTR, y)
    y[DIM] = x[DIM]
    return
