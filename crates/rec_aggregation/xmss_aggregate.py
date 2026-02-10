from snark_lib import *

V = V_PLACEHOLDER
V_GRINDING = V_GRINDING_PLACEHOLDER
W = W_PLACEHOLDER
CHAIN_LENGTH = 2 ** W
TARGET_SUM = TARGET_SUM_PLACEHOLDER
LOG_LIFETIME = LOG_LIFETIME_PLACEHOLDER
MESSAGE_LEN = MESSAGE_LEN_PLACEHOLDER
DIGEST_LEN = 8
RANDOMNESS_LEN = RANDOMNESS_LEN_PLACEHOLDER
SIG_SIZE = RANDOMNESS_LEN + (V + LOG_LIFETIME) * DIGEST_LEN
NUM_ENCODING_FE = div_ceil((V + V_GRINDING), (24 / W)) # 24 should be divisible by W (works for W=2,3,4)

# Dot product precompile:
DIM = 5
BE = 1  # base-extension (unused for XMSS)
EE = 0  # extension-extension


def main():
    pub_mem = NONRESERVED_PROGRAM_INPUT_START
    signatures_start: Imu
    hint_private_input_start(signatures_start)
    n_signatures = pub_mem[0]
    message = pub_mem + 1
    slot_ptr = message + MESSAGE_LEN
    slot_lo = slot_ptr[0]
    slot_hi = slot_ptr[1]
    merkle_indexes = slot_ptr + 2 # is left ?
    all_public_keys = merkle_indexes + LOG_LIFETIME

    for i in range(0, n_signatures):
        merkle_root = all_public_keys + i * DIGEST_LEN
        signature = signatures_start + SIG_SIZE * i
        xmss_verify(merkle_root, message, signature, slot_lo, slot_hi, merkle_indexes)
    return


def xmss_verify(merkle_root, message, signature, slot_lo, slot_hi, merkle_indexes):
    # signature: randomness | chain_tips | merkle_path
    # return the hashed xmss public key
    randomness = signature
    chain_starts = signature + RANDOMNESS_LEN
    merkle_path = chain_starts + V * DIGEST_LEN

    # 1) We encode message_hash + randomness into the layer of the hypercube with target sum = TARGET_SUM

    a_input_right = Array(DIGEST_LEN)
    b_input = Array(DIGEST_LEN * 2)
    a_input_right[0] = message[8]
    copy_7(randomness, a_input_right + 1)
    poseidon16(message, a_input_right, b_input)
    b_input[8] = slot_lo
    b_input[9] = slot_hi
    copy_6(merkle_root, b_input + 10)
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
    merkle_verify(wots_pubkey_hashed, merkle_path, merkle_indexes, LOG_LIFETIME, merkle_root)
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
def merkle_verify(leaf_digest, merkle_path, leaf_position_bits, height, expected_root):
    states = Array((height - 1) * DIGEST_LEN)

    # First merkle round
    match leaf_position_bits[0]:
        case 0:
            poseidon16(merkle_path, leaf_digest, states)
        case 1:
            poseidon16(leaf_digest, merkle_path, states)

    # Middle merkle rounds
    state_indexes = Array(height - 1)
    state_indexes[0] = states
    for j in unroll(1, height - 1):
        state_indexes[j] = state_indexes[j - 1] + DIGEST_LEN
        # Warning: this works only if leaf_position_bits[j] is known to be boolean:
        match leaf_position_bits[j]:
            case 0:
                poseidon16(
                    merkle_path + j * DIGEST_LEN,
                    state_indexes[j - 1],
                    state_indexes[j],
                )
            case 1:
                poseidon16(
                    state_indexes[j - 1],
                    merkle_path + j * DIGEST_LEN,
                    state_indexes[j],
                )

    # Final merkle round
    match leaf_position_bits[height - 1]:
        case 0:
            poseidon16(
                merkle_path + (height - 1) * DIGEST_LEN,
                state_indexes[height - 2],
                expected_root,
            )
        case 1:
            poseidon16(
                state_indexes[height - 2],
                merkle_path + (height - 1) * DIGEST_LEN,
                expected_root,
            )
    return


@inline
def slice_hash(data, len):
    states = Array((len-1) * DIGEST_LEN)
    poseidon16(data, data + DIGEST_LEN, states)
    state_indexes = Array(len - 1)
    state_indexes[0] = states
    for i in unroll(1, len-1):
        state_indexes[i] = state_indexes[i - 1] + DIGEST_LEN
        poseidon16(state_indexes[i - 1], data + DIGEST_LEN * (i + 1), state_indexes[i])
    return state_indexes[len - 2]


@inline
def copy_8(x, y):
    dot_product(x, ONE_VEC_PTR, y, 1, EE)
    dot_product(x + (8 - DIM), ONE_VEC_PTR, y + (8 - DIM), 1, EE)
    return


@inline
def copy_7(x, y):
    dot_product(x, ONE_VEC_PTR, y, 1, EE)
    dot_product(x + (7-DIM), ONE_VEC_PTR, y + (7-DIM), 1, EE)
    return


@inline
def copy_6(x, y):
    dot_product(x, ONE_VEC_PTR, y, 1, EE)
    y[5] = x[5]
    return


def print_digest(digest):
    for i in unroll(0, DIGEST_LEN):
        print(digest[i])
    return