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

    encoding = Array(NUM_ENCODING_FE * 24 / W)
    remaining = Array(NUM_ENCODING_FE)

    # TODO: decompose by chunks of 2.w bits (or even 3.w bits) and use a big match on the w^2 (or w^3) possibilities
    hint_decompose_bits_xmss(
        encoding,
        remaining,
        encoding_fe,
        NUM_ENCODING_FE,
        W
    )

    # check that the decomposition is correct
    for i in unroll(0, NUM_ENCODING_FE):
        for j in unroll(0, 24 / W):
            assert encoding[i * (24 / W) + j] < CHAIN_LENGTH

        assert remaining[i] < 2**7 - 1

        partial_sum: Mut = remaining[i] * 2**24
        for j in unroll(0, 24/W):
            partial_sum += encoding[i * (24 / W) + j] * CHAIN_LENGTH ** j
        assert partial_sum == encoding_fe[i]

    # we need to check the target sum
    target_sum: Mut = encoding[0]
    for i in unroll(1, V):
        target_sum += encoding[i]
    assert target_sum == TARGET_SUM

    # grinding
    for i in unroll(V, V + V_GRINDING):
        assert encoding[i] == CHAIN_LENGTH - 1

    wots_public_key = Array(V * DIGEST_LEN)

    for i in unroll(0, V):
        num_hashes = (CHAIN_LENGTH - 1) - encoding[i]
        chain_start = chain_starts + i * DIGEST_LEN
        chain_end = wots_public_key + i * DIGEST_LEN
        match_range(num_hashes,
                    range(0, 1), lambda _: copy_8(chain_start, chain_end),
                    range(1, 2), lambda _: poseidon16(chain_start, ZERO_VEC_PTR, chain_end),
                    range(2, CHAIN_LENGTH), lambda num_hashes_const: chain_hash(chain_start, num_hashes_const, chain_end))

    wots_pubkey_hashed = slice_hash(wots_public_key, V)
    xmss_merkle_verify(wots_pubkey_hashed, merkle_path, merkle_chunks, merkle_root)
    return


def chain_hash(input, n: Const, output):
    debug_assert(2 <= n)
    states = Array((n-1) * DIGEST_LEN)
    poseidon16(input, ZERO_VEC_PTR, states)
    state_indexes = Array(n - 1)
    state_indexes[0] = states
    for i in unroll(1, n-1):
        state_indexes[i] = state_indexes[i - 1] + DIGEST_LEN
        poseidon16(state_indexes[i - 1], ZERO_VEC_PTR, state_indexes[i])
    poseidon16(state_indexes[n - 2], ZERO_VEC_PTR, output)
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
