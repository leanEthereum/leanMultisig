from snark_lib import *

V = 66
W = 4
TARGET_SUM = 118
MAX_LOG_LIFETIME = 30

V_HALF = V / 2  # V should be even

VECTOR_LEN = 8

# Dot product precompile:
BE = 1  # base-extension
EE = 0  # extension-extension


def main():
    pub_mem = NONRESERVED_PROGRAM_INPUT_START
    signatures_start = pub_mem[0]
    n_signatures = pub_mem[1]
    message_hash = pub_mem + 2
    all_public_keys = message_hash + VECTOR_LEN
    all_log_lifetimes = all_public_keys + n_signatures * VECTOR_LEN
    all_merkle_indexes = all_log_lifetimes + n_signatures
    sig_sizes = all_merkle_indexes + n_signatures * MAX_LOG_LIFETIME

    for i in range(0, n_signatures):
        xmss_public_key = all_public_keys + i * VECTOR_LEN
        signature = signatures_start + sig_sizes[i]
        log_lifetime = all_log_lifetimes[i]
        merkle_index = all_merkle_indexes + i * MAX_LOG_LIFETIME
        xmss_public_key_recovered = xmss_recover_pub_key(message_hash, signature, log_lifetime, merkle_index)
        assert_eq_vec(xmss_public_key, xmss_public_key_recovered)
    return


def xmss_recover_pub_key(message_hash, signature, log_lifetime, merkle_index):
    # signature: randomness | chain_tips
    # return the hashed xmss public key
    randomness = signature
    chain_tips = signature + VECTOR_LEN
    merkle_path = chain_tips + V * VECTOR_LEN

    # 1) We encode message_hash + randomness into the d-th layer of the hypercube

    compressed = Array(VECTOR_LEN)
    poseidon16(message_hash, randomness, compressed)
    compressed_vals = Array(6)
    dot_product(compressed, ONE_VEC_PTR, compressed_vals, 1, EE)
    compressed_vals[5] = compressed[5]

    encoding = Array(12 * 6)
    remaining = Array(6)

    hint_decompose_bits_xmss(
        encoding,
        remaining,
        compressed_vals[0],
        compressed_vals[1],
        compressed_vals[2],
        compressed_vals[3],
        compressed_vals[4],
        compressed_vals[5],
    )

    # check that the decomposition is correct
    for i in unroll(0, 6):
        for j in unroll(0, 12):
            assert encoding[i * 12 + j] <= 3

        assert remaining[i] <= 2**7 - 2

        partial_sum: Mut = remaining[i] * 2**24
        for j in unroll(1, 13):
            partial_sum += encoding[i * 12 + (j - 1)] * 4 ** (j - 1)
        assert partial_sum == compressed_vals[i]

    # we need to check the target sum
    target_sum: Mut = encoding[0]
    for i in unroll(1, V):
        target_sum += encoding[i]
    assert target_sum == TARGET_SUM

    public_key = Array(V * VECTOR_LEN)

    # This is a trick to avoid the compiler to allocate memory "on stack".
    # (Heap allocation is better here, to keep the memmory use of the different "match arms" balanced)
    vector_len = VECTOR_LEN

    for i in unroll(0, V):
        match encoding[i]:
            case 0:
                var_1 = chain_tips + i * VECTOR_LEN
                var_2 = public_key + i * VECTOR_LEN
                var_3 = Array(vector_len)
                var_4 = Array(vector_len)
                poseidon16(var_1, ZERO_VEC_PTR, var_3)
                poseidon16(var_3, ZERO_VEC_PTR, var_4)
                poseidon16(var_4, ZERO_VEC_PTR, var_2)
            case 1:
                var_3 = Array(vector_len)
                var_1 = chain_tips + i * VECTOR_LEN
                var_2 = public_key + i * VECTOR_LEN
                poseidon16(var_1, ZERO_VEC_PTR, var_3)
                poseidon16(var_3, ZERO_VEC_PTR, var_2)
            case 2:
                var_1 = chain_tips + i * VECTOR_LEN
                var_2 = public_key + i * VECTOR_LEN
                poseidon16(var_1, ZERO_VEC_PTR, var_2)
            case 3:
                var_1 = chain_tips + (i * VECTOR_LEN)
                var_2 = public_key + (i * VECTOR_LEN)
                var_3 = var_1 + 3
                var_4 = var_2 + 3
                dot_product(var_1, ONE_VEC_PTR, var_2, 1, EE)
                dot_product(var_3, ONE_VEC_PTR, var_4, 1, EE)

    wots_pubkey_hashed = slice_hash(ZERO_VEC_PTR, public_key, V_HALF)

    debug_assert(log_lifetime < MAX_LOG_LIFETIME + 1)

    merkle_root: Imu
    match log_lifetime:
        case 0:
            merkle_root = merkle_verify(wots_pubkey_hashed, merkle_path, merkle_index, 0)
        case 1:
            merkle_root = merkle_verify(wots_pubkey_hashed, merkle_path, merkle_index, 1)
        case 2:
            merkle_root = merkle_verify(wots_pubkey_hashed, merkle_path, merkle_index, 2)
        case 3:
            merkle_root = merkle_verify(wots_pubkey_hashed, merkle_path, merkle_index, 3)
        case 4:
            merkle_root = merkle_verify(wots_pubkey_hashed, merkle_path, merkle_index, 4)
        case 5:
            merkle_root = merkle_verify(wots_pubkey_hashed, merkle_path, merkle_index, 5)
        case 6:
            merkle_root = merkle_verify(wots_pubkey_hashed, merkle_path, merkle_index, 6)
        case 7:
            merkle_root = merkle_verify(wots_pubkey_hashed, merkle_path, merkle_index, 7)
        case 8:
            merkle_root = merkle_verify(wots_pubkey_hashed, merkle_path, merkle_index, 8)
        case 9:
            merkle_root = merkle_verify(wots_pubkey_hashed, merkle_path, merkle_index, 9)
        case 10:
            merkle_root = merkle_verify(wots_pubkey_hashed, merkle_path, merkle_index, 10)
        case 11:
            merkle_root = merkle_verify(wots_pubkey_hashed, merkle_path, merkle_index, 11)
        case 12:
            merkle_root = merkle_verify(wots_pubkey_hashed, merkle_path, merkle_index, 12)
        case 13:
            merkle_root = merkle_verify(wots_pubkey_hashed, merkle_path, merkle_index, 13)
        case 14:
            merkle_root = merkle_verify(wots_pubkey_hashed, merkle_path, merkle_index, 14)
        case 15:
            merkle_root = merkle_verify(wots_pubkey_hashed, merkle_path, merkle_index, 15)
        case 16:
            merkle_root = merkle_verify(wots_pubkey_hashed, merkle_path, merkle_index, 16)
        case 17:
            merkle_root = merkle_verify(wots_pubkey_hashed, merkle_path, merkle_index, 17)
        case 18:
            merkle_root = merkle_verify(wots_pubkey_hashed, merkle_path, merkle_index, 18)
        case 19:
            merkle_root = merkle_verify(wots_pubkey_hashed, merkle_path, merkle_index, 19)
        case 20:
            merkle_root = merkle_verify(wots_pubkey_hashed, merkle_path, merkle_index, 20)
        case 21:
            merkle_root = merkle_verify(wots_pubkey_hashed, merkle_path, merkle_index, 21)
        case 22:
            merkle_root = merkle_verify(wots_pubkey_hashed, merkle_path, merkle_index, 22)
        case 23:
            merkle_root = merkle_verify(wots_pubkey_hashed, merkle_path, merkle_index, 23)
        case 24:
            merkle_root = merkle_verify(wots_pubkey_hashed, merkle_path, merkle_index, 24)
        case 25:
            merkle_root = merkle_verify(wots_pubkey_hashed, merkle_path, merkle_index, 25)
        case 26:
            merkle_root = merkle_verify(wots_pubkey_hashed, merkle_path, merkle_index, 26)
        case 27:
            merkle_root = merkle_verify(wots_pubkey_hashed, merkle_path, merkle_index, 27)
        case 28:
            merkle_root = merkle_verify(wots_pubkey_hashed, merkle_path, merkle_index, 28)
        case 29:
            merkle_root = merkle_verify(wots_pubkey_hashed, merkle_path, merkle_index, 29)
        case 30:
            merkle_root = merkle_verify(wots_pubkey_hashed, merkle_path, merkle_index, 30)
        case 31:
            merkle_root = merkle_verify(wots_pubkey_hashed, merkle_path, merkle_index, 31)
        case 32:
            merkle_root = merkle_verify(wots_pubkey_hashed, merkle_path, merkle_index, 32)

    return merkle_root


def merkle_verify(leaf_digest, merkle_path, leaf_position_bits, height: Const):
    states = Array(height * VECTOR_LEN)

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
        state_indexes[j] = state_indexes[j - 1] + VECTOR_LEN
        # Warning: this works only if leaf_position_bits[i] is known to be boolean:
        match leaf_position_bits[j]:
            case 0:
                poseidon16(
                    state_indexes[j - 1],
                    merkle_path + j * VECTOR_LEN,
                    state_indexes[j],
                )
            case 1:
                poseidon16(
                    merkle_path + j * VECTOR_LEN,
                    state_indexes[j - 1],
                    state_indexes[j],
                )
    return state_indexes[height - 1]


def slice_hash(seed, data, half_len: Const):
    states = Array(half_len * 2 * VECTOR_LEN)
    poseidon16(ZERO_VEC_PTR, data, states)
    state_indexes = Array(half_len * 2)
    state_indexes[0] = states
    for j in unroll(1, (half_len * 2)):
        state_indexes[j] = state_indexes[j - 1] + VECTOR_LEN
        poseidon16(state_indexes[j - 1], data + j * VECTOR_LEN, state_indexes[j])
    return state_indexes[half_len * 2 - 1]


@inline
def assert_eq_vec(x, y):
    dot_product(x, ONE_VEC_PTR, y, 1, EE)
    dot_product(x + 3, ONE_VEC_PTR, y + 3, 1, EE)
    return
