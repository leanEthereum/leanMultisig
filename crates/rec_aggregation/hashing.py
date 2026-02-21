from snark_lib import *

DIM = 5  # extension degree
DIGEST_LEN = 8

# bit decomposition hint
LITTLE_ENDIAN = 1
BIG_ENDIAN = 0

def batch_hash_slice_rtl(num_queries, all_data_to_hash, all_resulting_hashes, num_chunks):
    if num_chunks == DIM * 2:
        batch_hash_slice_rtl_const(num_queries, all_data_to_hash, all_resulting_hashes, DIM * 2)
        return
    if num_chunks == 16:
        batch_hash_slice_rtl_const(num_queries, all_data_to_hash, all_resulting_hashes, 16)
        return
    if num_chunks == 8:
        batch_hash_slice_rtl_const(num_queries, all_data_to_hash, all_resulting_hashes, 8)
        return
    if num_chunks == 20:
        batch_hash_slice_rtl_const(num_queries, all_data_to_hash, all_resulting_hashes, 20)
        return
    if num_chunks == 1:
        batch_hash_slice_rtl_const(num_queries, all_data_to_hash, all_resulting_hashes, 1)
        return
    if num_chunks == 4:
        batch_hash_slice_rtl_const(num_queries, all_data_to_hash, all_resulting_hashes, 4)
        return
    if num_chunks == 5:
        batch_hash_slice_rtl_const(num_queries, all_data_to_hash, all_resulting_hashes, 5)
        return
    print(num_chunks)
    assert False, "batch_hash_slice called with unsupported len"


def batch_hash_slice_rtl_const(num_queries, all_data_to_hash, all_resulting_hashes, num_chunks: Const):
    for i in range(0, num_queries):
        data = all_data_to_hash[i]
        res = slice_hash_rtl(data, num_chunks)
        all_resulting_hashes[i] = res
    return


@inline
def slice_hash_rtl(data, num_chunks):
    states = Array((num_chunks - 1) * DIGEST_LEN)
    poseidon16(data + (num_chunks - 2) * DIGEST_LEN, data + (num_chunks - 1) * DIGEST_LEN, states)
    state_indexes = Array(num_chunks)
    state_indexes[0] = states
    for j in unroll(1, num_chunks - 1):
        state_indexes[j] = state_indexes[j - 1] + DIGEST_LEN
        poseidon16(state_indexes[j - 1], data + (num_chunks - 2 - j) * DIGEST_LEN, state_indexes[j])
    return state_indexes[num_chunks - 2]


@inline
def slice_hash(data, num_chunks):
    states = Array((num_chunks - 1) * DIGEST_LEN)
    poseidon16(data, data + DIGEST_LEN, states)
    for j in unroll(1, num_chunks - 1):
        poseidon16(states + (j - 1) * DIGEST_LEN, data + (j + 1) * DIGEST_LEN, states + j * DIGEST_LEN)
    return states + (num_chunks - 2) * DIGEST_LEN


def slice_hash_dynamic_unroll(data, len, len_bits: Const):
    remainder = modulo_8(len, len_bits)
    num_full_elements = len - remainder
    num_full_chunks = num_full_elements / 8

    if num_full_chunks == 0:
        left = Array(DIGEST_LEN)
        fill_padded_chunk(left, data, remainder)
        result = Array(DIGEST_LEN)
        poseidon16(left, ZERO_VEC_PTR, result)
        return result

    if num_full_chunks == 1:
        if remainder == 0:
            result = Array(DIGEST_LEN)
            poseidon16(data, ZERO_VEC_PTR, result)
            return result
        else:
            right = Array(DIGEST_LEN)
            fill_padded_chunk(right, data + DIGEST_LEN, remainder)
            result = Array(DIGEST_LEN)
            poseidon16(data, right, result)
            return result

    if remainder == 0:
        return slice_hash_chunks(data, num_full_chunks, len_bits)
    else:
        hash = slice_hash_chunks(data, num_full_chunks, len_bits)
        padded_last = Array(DIGEST_LEN)
        fill_padded_chunk(padded_last, data + num_full_elements, remainder)
        final_hash = Array(DIGEST_LEN)
        poseidon16(hash, padded_last, final_hash)
        return final_hash


def slice_hash_chunks(data, num_chunks, num_chunks_bits: Const):
    debug_assert(1 < num_chunks)
    states = Array((num_chunks - 1) * DIGEST_LEN)
    poseidon16(data, data + DIGEST_LEN, states)
    n_iters = num_chunks - 2
    for j in dynamic_unroll(0, n_iters, num_chunks_bits):
        poseidon16(states + j * DIGEST_LEN, data + (j + 2) * DIGEST_LEN, states + (j + 1) * DIGEST_LEN)
    return states + (num_chunks - 2) * DIGEST_LEN


def fill_padded_chunk(dst, src, n):
    debug_assert(0 < n)
    debug_assert(n < DIGEST_LEN)
    match_range(n, range(1, DIGEST_LEN), lambda r: fill_padded_chunk_const(dst, src, r))
    return

def fill_padded_chunk_const(dst, src, n: Const):
    for i in unroll(0, n):
        dst[i] = src[i]
    for i in unroll(n, DIGEST_LEN):
        dst[i] = 0
    return


def modulo_8(n, n_bits: Const):
    debug_assert(2 < n_bits)
    debug_assert(n < 2**n_bits)
    bits = Array(n_bits)
    hint_decompose_bits(n, bits, n_bits, BIG_ENDIAN)
    partial_sums = Array(n_bits)
    partial_sums[0] = bits[n_bits - 1]
    assert partial_sums[0] * (1 - partial_sums[0]) == 0
    for i in unroll(1, n_bits):
        b = bits[n_bits - 1 - i]
        assert b * (1 - b) == 0
        partial_sums[i] = partial_sums[i - 1] + b * 2**i
    assert n == partial_sums[n_bits - 1]
    return partial_sums[2]


def merkle_verif_batch(merkle_paths, leaves_digests, leave_positions, root, height, num_queries):
    match_range(height, range(10, 26), lambda h: merkle_verif_batch_const(
        num_queries,
        merkle_paths,
        leaves_digests,
        leave_positions,
        root,
        h,
    ))
    return


def merkle_verif_batch_const(n_paths, merkle_paths, leaves_digests, leave_positions, root, height: Const):
    # n_paths: F
    # leaves_digests: pointer to a slice of n_paths vectorized pointers, each pointing to 1 chunk of 8 field elements
    # leave_positions: pointer to a slice of n_paths field elements (each < 2^height)
    # root: vectorized pointer to 1 chunk of 8 field elements
    # height: F

    for i in range(0, n_paths):
        merkle_verify(
            leaves_digests[i],
            merkle_paths + (i * height) * DIGEST_LEN,
            leave_positions[i],
            root,
            height,
        )

    return


def merkle_verify(leaf_digest, merkle_path, leaf_position_bits, root, height: Const):
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
    copy_8(state_indexes[height - 1], root)
    return
