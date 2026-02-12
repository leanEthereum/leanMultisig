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
    debug_assert(V % 2 == 0) # current implem only supports even V (cf "V / 2" bellow)
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

    for i in unroll(0, V / 2):
        pair_val = encoding[2 * i] + encoding[2 * i + 1] * CHAIN_LENGTH
        chain_start_left = chain_starts + (2 * i) * DIGEST_LEN
        chain_end_left = wots_public_key + (2 * i) * DIGEST_LEN
        match_range(pair_val,
                    range(0, CHAIN_LENGTH ** 2),
                    lambda pv: handle_wots_pair(pv, chain_start_left, chain_end_left))

    wots_pubkey_hashed = slice_hash(wots_public_key, V)
    merkle_verify(wots_pubkey_hashed, merkle_path, merkle_indexes, LOG_LIFETIME, merkle_root)
    return


def handle_wots_pair(pv: Const, chain_start_left, chain_end_left):
    chain_start_right = chain_start_left + DIGEST_LEN
    chain_end_right = chain_end_left + DIGEST_LEN
    left_enc = pv % CHAIN_LENGTH
    right_enc = (pv - left_enc) / CHAIN_LENGTH
    num_left = (CHAIN_LENGTH - 1) - left_enc
    num_right = (CHAIN_LENGTH - 1) - right_enc

    # Left chain
    if num_left == 0:
        copy_8(chain_start_left, chain_end_left)
    else if num_left == 1:
        poseidon16(chain_start_left, ZERO_VEC_PTR, chain_end_left)
    else if num_left == 2:
        tmp_l = Array(DIGEST_LEN)
        poseidon16(chain_start_left, ZERO_VEC_PTR, tmp_l)
        poseidon16(tmp_l, ZERO_VEC_PTR, chain_end_left)
    else if num_left == 3:
        tmp_l = Array(2 * DIGEST_LEN)
        poseidon16(chain_start_left, ZERO_VEC_PTR, tmp_l)
        poseidon16(tmp_l, ZERO_VEC_PTR, tmp_l + DIGEST_LEN)
        poseidon16(tmp_l + DIGEST_LEN, ZERO_VEC_PTR, chain_end_left)
    else:
        states_l = Array((num_left - 1) * DIGEST_LEN)
        poseidon16(chain_start_left, ZERO_VEC_PTR, states_l)
        si_l = Array(num_left - 1)
        si_l[0] = states_l
        for k in unroll(1, num_left - 1):
            si_l[k] = si_l[k - 1] + DIGEST_LEN
            poseidon16(si_l[k - 1], ZERO_VEC_PTR, si_l[k])
        poseidon16(si_l[num_left - 2], ZERO_VEC_PTR, chain_end_left)

    # Right chain
    if num_right == 0:
        copy_8(chain_start_right, chain_end_right)
    else if num_right == 1:
        poseidon16(chain_start_right, ZERO_VEC_PTR, chain_end_right)
    else if num_right == 2:
        tmp_r = Array(DIGEST_LEN)
        poseidon16(chain_start_right, ZERO_VEC_PTR, tmp_r)
        poseidon16(tmp_r, ZERO_VEC_PTR, chain_end_right)
    else if num_right == 3:
        tmp_r = Array(2 * DIGEST_LEN)
        poseidon16(chain_start_right, ZERO_VEC_PTR, tmp_r)
        poseidon16(tmp_r, ZERO_VEC_PTR, tmp_r + DIGEST_LEN)
        poseidon16(tmp_r + DIGEST_LEN, ZERO_VEC_PTR, chain_end_right)
    else:
        states_r = Array((num_right - 1) * DIGEST_LEN)
        poseidon16(chain_start_right, ZERO_VEC_PTR, states_r)
        si_r = Array(num_right - 1)
        si_r[0] = states_r
        for k in unroll(1, num_right - 1):
            si_r[k] = si_r[k - 1] + DIGEST_LEN
            poseidon16(si_r[k - 1], ZERO_VEC_PTR, si_r[k])
        poseidon16(si_r[num_right - 2], ZERO_VEC_PTR, chain_end_right)

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