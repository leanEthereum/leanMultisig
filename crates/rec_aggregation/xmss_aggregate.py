from snark_lib import *

V = V_PLACEHOLDER
V_GRINDING = V_GRINDING_PLACEHOLDER
W = W_PLACEHOLDER
CHAIN_LENGTH = 2 ** W
TARGET_SUM = TARGET_SUM_PLACEHOLDER
LOG_LIFETIME = LOG_LIFETIME_PLACEHOLDER
MESSAGE_LEN = MESSAGE_LEN_PLACEHOLDER
DIGEST_LEN = 8
RANDOMNESS_LEN = 8
SIG_SIZE = RANDOMNESS_LEN + (V + LOG_LIFETIME) * DIGEST_LEN
NUM_ENCODING_FE = div_ceil((V + V_GRINDING), (24 / W)) # 24 should be divisible by W (works for W=2,3,4)

# Dot product precompile:
DIM = 5
BE = 1  # base-extension (unused for XMSS)
EE = 0  # extension-extension


def main():
    pub_mem = NONRESERVED_PROGRAM_INPUT_START
    signatures_start = pub_mem[0]
    n_signatures = pub_mem[1]
    message = pub_mem + 2
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
    chain_tips = signature + RANDOMNESS_LEN
    merkle_path = chain_tips + V * DIGEST_LEN

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
        match_range(num_hashes,
                    range(0, 1), lambda _: copy_8(chain_tips + i * DIGEST_LEN, wots_public_key + i * DIGEST_LEN),
                    range(1, 2), lambda _: poseidon16(chain_tips + i * DIGEST_LEN, ZERO_VEC_PTR, wots_public_key + i * DIGEST_LEN),
                    range(2, CHAIN_LENGTH), lambda num_hashes_const: chain_hash(chain_tips + i * DIGEST_LEN, num_hashes_const, wots_public_key + i * DIGEST_LEN))
        
    wots_pubkey_hashed = slice_hash(wots_public_key, V)
    merkle_root_recovered = merkle_verify(wots_pubkey_hashed, merkle_path, merkle_indexes, LOG_LIFETIME)
    copy_8(merkle_root, merkle_root_recovered)
    return


def chain_hash(input, n: Const, output):
    debug_assert(2 < n)
    states = Array((n-1) * DIGEST_LEN)
    poseidon16(input, ZERO_VEC_PTR, states)
    for i in unroll(1, n-1):
        poseidon16(states + (i - 1) * DIGEST_LEN, ZERO_VEC_PTR, states + i * DIGEST_LEN)
    poseidon16(states + (n - 2) * DIGEST_LEN, ZERO_VEC_PTR, output)
    return


@inline
def merkle_verify(leaf_digest, merkle_path, leaf_position_bits, height):
    states = Array(height * DIGEST_LEN)

    # First merkle round
    match leaf_position_bits[0]:
        case 0:
            poseidon16(leaf_digest, merkle_path, states)
        case 1:
            poseidon16(merkle_path, leaf_digest, states)

    # Remaining merkle rounds
    state_indexes = Array(height)
    state_indexes[0] = states
    for j in unroll(1, height):
        state_indexes[j] = state_indexes[j - 1] + DIGEST_LEN
        # Warning: this works only if leaf_position_bits[i] is known to be boolean:
        match leaf_position_bits[j]:
            case 0:
                poseidon16(
                    state_indexes[j - 1],
                    merkle_path + j * DIGEST_LEN,
                    state_indexes[j],
                )
            case 1:
                poseidon16(
                    merkle_path + j * DIGEST_LEN,
                    state_indexes[j - 1],
                    state_indexes[j],
                )
    return state_indexes[height - 1]


def slice_hash(data, len: Const):
    states = Array((len-1) * DIGEST_LEN)
    poseidon16(data, data + DIGEST_LEN, states)
    for i in unroll(1, len-1):
        poseidon16(states + (i - 1) * DIGEST_LEN, data + DIGEST_LEN * (i + 1), states + i * DIGEST_LEN)
    return data


@inline
def copy_8(x, y):
    dot_product(x, ONE_VEC_PTR, y, 1, EE)
    dot_product(x + (8 - DIM), ONE_VEC_PTR, y + (8 - DIM), 1, EE)
    return


@inline
def copy_7(x, y):
    dot_product(x, ONE_VEC_PTR, y, 1, EE)
    x[5] = y[5]
    y[6] = x[6]
    return


@inline
def copy_6(x, y):
    dot_product(x, ONE_VEC_PTR, y, 1, EE)
    x[5] = y[5]
    return
