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

    for i in unroll(0, V / 2):
        # num_hashes = (CHAIN_LENGTH - 1) - encoding[i]
        chain_start = chain_starts + i * (DIGEST_LEN * 2)
        chain_end = wots_public_key + i * (DIGEST_LEN * 2)
        pair_chain_length_sum_ptr = Array(1)
        match_range(encoding[i], range(0, CHAIN_LENGTH**2), lambda n: chain_hash(chain_start, n, chain_end, pair_chain_length_sum_ptr))
        target_sum += pair_chain_length_sum_ptr[0]

    assert target_sum == TARGET_SUM

    wots_pubkey_hashed = slice_hash(wots_public_key, V)
    xmss_merkle_verify(wots_pubkey_hashed, merkle_path, merkle_chunks, merkle_root)
    return


def chain_hash(input_left, n: Const, output_left, pair_chain_length_sum_ptr):
    debug_assert(n < CHAIN_LENGTH**2)

    raw_left = n % CHAIN_LENGTH
    raw_right = (n - raw_left) / CHAIN_LENGTH

    n_left = (CHAIN_LENGTH - 1) - raw_left
    if n_left == 0:
        copy_8(input_left, output_left)
    else if n_left == 1:
        poseidon16(input_left, ZERO_VEC_PTR, output_left)
    else:
        states_left = Array((n_left-1) * DIGEST_LEN)
        poseidon16(input_left, ZERO_VEC_PTR, states_left)
        state_indexes_left = Array(n_left - 1)
        state_indexes_left[0] = states_left
        for i in unroll(1, n_left-1):
            state_indexes_left[i] = state_indexes_left[i - 1] + DIGEST_LEN
            poseidon16(state_indexes_left[i - 1], ZERO_VEC_PTR, state_indexes_left[i])
        poseidon16(state_indexes_left[n_left - 2], ZERO_VEC_PTR, output_left)

    n_right = (CHAIN_LENGTH - 1) - raw_right
    debug_assert(raw_right < CHAIN_LENGTH)
    input_right = input_left + DIGEST_LEN
    output_right = output_left + DIGEST_LEN
    if n_right == 0:
        copy_8(input_right, output_right)
    else if n_right == 1:
        poseidon16(input_right, ZERO_VEC_PTR, output_right)
    else:
        states_right = Array((n_right-1) * DIGEST_LEN)
        poseidon16(input_right, ZERO_VEC_PTR, states_right)
        state_indexes_right = Array(n_right - 1)
        state_indexes_right[0] = states_right
        for i in unroll(1, n_right-1):
            state_indexes_right[i] = state_indexes_right[i - 1] + DIGEST_LEN
            poseidon16(state_indexes_right[i - 1], ZERO_VEC_PTR, state_indexes_right[i])
        poseidon16(state_indexes_right[n_right - 2], ZERO_VEC_PTR, output_right)

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
    temp_indexes = Array(3)

    # Level 0: state_in -> temps
    if b0 == 0:
        poseidon16(path_chunk, state_in, temps)
    else:
        poseidon16(state_in, path_chunk, temps)

    temp_indexes[0] = temps

    # Level 1
    temp_indexes[1] = temp_indexes[0] + DIGEST_LEN
    if b1 == 0:
        poseidon16(path_chunk + 1 * DIGEST_LEN, temp_indexes[0], temp_indexes[1])
    else:
        poseidon16(temp_indexes[0], path_chunk + 1 * DIGEST_LEN, temp_indexes[1])

    # Level 2
    temp_indexes[2] = temp_indexes[1] + DIGEST_LEN
    if b2 == 0:
        poseidon16(path_chunk + 2 * DIGEST_LEN, temp_indexes[1], temp_indexes[2])
    else:
        poseidon16(temp_indexes[1], path_chunk + 2 * DIGEST_LEN, temp_indexes[2])

    # Level 3: -> state_out
    if b3 == 0:
        poseidon16(path_chunk + 3 * DIGEST_LEN, temp_indexes[2], state_out)
    else:
        poseidon16(temp_indexes[2], path_chunk + 3 * DIGEST_LEN, state_out)
    return


@inline
def xmss_merkle_verify(leaf_digest, merkle_path, merkle_chunks, expected_root):
    states = Array((N_MERKLE_CHUNKS - 1) * DIGEST_LEN)

    # First chunk: leaf_digest -> states
    match_range(merkle_chunks[0], range(0, 16), lambda b: do_4_merkle_levels(b, leaf_digest, merkle_path, states))

    # Middle chunks
    state_indexes = Array(N_MERKLE_CHUNKS - 1)
    state_indexes[0] = states
    for j in unroll(1, N_MERKLE_CHUNKS - 1):
        state_indexes[j] = state_indexes[j - 1] + DIGEST_LEN
        match_range(merkle_chunks[j], range(0, 16), lambda b: do_4_merkle_levels(b, state_indexes[j - 1], merkle_path + j * MERKLE_LEVELS_PER_CHUNK * DIGEST_LEN, state_indexes[j]))

    # Last chunk: -> expected_root
    match_range(merkle_chunks[N_MERKLE_CHUNKS - 1], range(0, 16), lambda b: do_4_merkle_levels(b, state_indexes[N_MERKLE_CHUNKS - 2], merkle_path + (N_MERKLE_CHUNKS - 1) * MERKLE_LEVELS_PER_CHUNK * DIGEST_LEN, expected_root))
    return


@inline
def copy_7(x, y):
    dot_product(x, ONE_VEC_PTR, y, 1, EE)
    dot_product(x + (7-DIM), ONE_VEC_PTR, y + (7-DIM), 1, EE)
    return


@inline
def copy_6(x, y):
    dot_product(x, ONE_VEC_PTR, y, 1, EE)
    y[DIM] = x[DIM]
    return
