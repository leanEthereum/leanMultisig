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
    for j in unroll(1, num_chunks - 1):
        poseidon16(states + (j - 1) * DIGEST_LEN, data + (num_chunks - 2 - j) * DIGEST_LEN, states + j * DIGEST_LEN)
    return states + (num_chunks - 2) * DIGEST_LEN



def slice_hash_rtl_with_initial_state(initial_state, data, n_effective, n_effective_bits: Const):
    debug_assert(0 < n_effective)
    if n_effective == 1:
        result = Array(DIGEST_LEN)
        poseidon16(initial_state, data, result)
        return result
    states = Array(n_effective * DIGEST_LEN)
    poseidon16(initial_state, data + (n_effective - 1) * DIGEST_LEN, states)
    n_iters = n_effective - 1
    state_ptr: Mut = states
    data_ptr: Mut = data + (n_effective - 2) * DIGEST_LEN
    for _ in dynamic_unroll(0, n_iters, n_effective_bits):
        new_state = state_ptr + DIGEST_LEN
        poseidon16(state_ptr, data_ptr, new_state)
        state_ptr = new_state
        data_ptr = data_ptr - DIGEST_LEN
    return state_ptr


@inline
def slice_hash(data, num_chunks):
    states = Array((num_chunks - 1) * DIGEST_LEN)
    poseidon16(data, data + DIGEST_LEN, states)
    for j in unroll(1, num_chunks - 1):
        poseidon16(states + (j - 1) * DIGEST_LEN, data + (j + 1) * DIGEST_LEN, states + j * DIGEST_LEN)
    return states + (num_chunks - 2) * DIGEST_LEN



def slice_hash_with_iv_dynamic_unroll(data, len, len_bits: Const):
    remainder = modulo_8(len, len_bits)
    num_full_elements = len - remainder
    num_full_chunks = num_full_elements / 8

    if num_full_chunks == 0:
        left = Array(DIGEST_LEN)
        fill_padded_chunk(left, data, remainder)
        result = Array(DIGEST_LEN)
        poseidon16(ZERO_VEC_PTR, left, result)
        return result

    if num_full_chunks == 1:
        if remainder == 0:
            result = Array(DIGEST_LEN)
            poseidon16(ZERO_VEC_PTR, data, result)
            return result
        else:
            h0 = Array(DIGEST_LEN)
            poseidon16(ZERO_VEC_PTR, data, h0)
            right = Array(DIGEST_LEN)
            fill_padded_chunk(right, data + DIGEST_LEN, remainder)
            result = Array(DIGEST_LEN)
            poseidon16(h0, right, result)
            return result

    partial_hash = slice_hash_chunks_with_iv(data, num_full_chunks, len_bits)
    if remainder == 0:
        return partial_hash
    else:
        padded_last = Array(DIGEST_LEN)
        fill_padded_chunk(padded_last, data + num_full_elements, remainder)
        final_hash = Array(DIGEST_LEN)
        poseidon16(partial_hash, padded_last, final_hash)
        return final_hash


@inline
def slice_hash_chunks_with_iv(data, num_chunks, num_chunks_bits):
    debug_assert(1 < num_chunks)
    states = Array(num_chunks * DIGEST_LEN)
    poseidon16(ZERO_VEC_PTR, data, states)
    n_iters = num_chunks - 1
    state_ptr: Mut = states
    data_ptr: Mut = data + DIGEST_LEN
    for _ in dynamic_unroll(0, n_iters, num_chunks_bits):
        new_state = state_ptr + DIGEST_LEN
        poseidon16(state_ptr, data_ptr, new_state)
        state_ptr = new_state
        data_ptr = data_ptr + DIGEST_LEN
    return state_ptr


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


@inline
def whir_do_4_merkle_levels(b, state_in, path_chunk, state_out):
    b0 = b % 2
    r1 = (b - b0) / 2
    b1 = r1 % 2
    r2 = (r1 - b1) / 2
    b2 = r2 % 2
    r3 = (r2 - b2) / 2
    b3 = r3 % 2

    temps = Array(3 * DIGEST_LEN)

    if b0 == 0:
        poseidon16(state_in, path_chunk, temps)
    else:
        poseidon16(path_chunk, state_in, temps)

    if b1 == 0:
        poseidon16(temps, path_chunk + DIGEST_LEN, temps + DIGEST_LEN)
    else:
        poseidon16(path_chunk + DIGEST_LEN, temps, temps + DIGEST_LEN)

    if b2 == 0:
        poseidon16(temps + DIGEST_LEN, path_chunk + 2 * DIGEST_LEN, temps + 2 * DIGEST_LEN)
    else:
        poseidon16(path_chunk + 2 * DIGEST_LEN, temps + DIGEST_LEN, temps + 2 * DIGEST_LEN)

    if b3 == 0:
        poseidon16(temps + 2 * DIGEST_LEN, path_chunk + 3 * DIGEST_LEN, state_out)
    else:
        poseidon16(path_chunk + 3 * DIGEST_LEN, temps + 2 * DIGEST_LEN, state_out)
    return

@inline
def whir_do_3_merkle_levels(b, state_in, path_chunk, state_out):
    b0 = b % 2
    r1 = (b - b0) / 2
    b1 = r1 % 2
    r2 = (r1 - b1) / 2
    b2 = r2 % 2

    temps = Array(2 * DIGEST_LEN)

    if b0 == 0:
        poseidon16(state_in, path_chunk, temps)
    else:
        poseidon16(path_chunk, state_in, temps)

    if b1 == 0:
        poseidon16(temps, path_chunk + DIGEST_LEN, temps + DIGEST_LEN)
    else:
        poseidon16(path_chunk + DIGEST_LEN, temps, temps + DIGEST_LEN)

    if b2 == 0:
        poseidon16(temps + DIGEST_LEN, path_chunk + 2 * DIGEST_LEN, state_out)
    else:
        poseidon16(path_chunk + 2 * DIGEST_LEN, temps + DIGEST_LEN, state_out)
    return


@inline
def whir_do_2_merkle_levels(b, state_in, path_chunk, state_out):
    b0 = b % 2
    r1 = (b - b0) / 2
    b1 = r1 % 2

    temp = Array(DIGEST_LEN)

    if b0 == 0:
        poseidon16(state_in, path_chunk, temp)
    else:
        poseidon16(path_chunk, state_in, temp)

    if b1 == 0:
        poseidon16(temp, path_chunk + DIGEST_LEN, state_out)
    else:
        poseidon16(path_chunk + DIGEST_LEN, temp, state_out)
    return


@inline
def whir_do_1_merkle_level(b, state_in, path_chunk, state_out):
    b0 = b % 2

    if b0 == 0:
        poseidon16(state_in, path_chunk, state_out)
    else:
        poseidon16(path_chunk, state_in, state_out)
    return


@inline
def hash_and_verify_merkle_hint(leaf_position_nibbles, root, height, num_chunks):
    # Hint and hash leaf
    leaf_data = Array(num_chunks * DIGEST_LEN)
    hint_merkle(leaf_data, num_chunks * DIGEST_LEN)
    leaf_hash = slice_hash_rtl(leaf_data, num_chunks)

    # Hint and verify merkle path (processing 4 levels per nibble)
    merkle_path = Array(height * DIGEST_LEN)
    hint_merkle(merkle_path, height * DIGEST_LEN)

    states = Array((div_ceil(height, 4) - 1) * DIGEST_LEN)

    # First full nibble: leaf_hash -> states[0]
    match_range(leaf_position_nibbles[0], range(0, 16),
        lambda b: whir_do_4_merkle_levels(b, leaf_hash, merkle_path, states))

    # Middle nibble chunks: states[k-1] -> states[k]
    for k in unroll(1, div_ceil(height, 4) - 1):
        match_range(leaf_position_nibbles[k], range(0, 16),
            lambda b: whir_do_4_merkle_levels(b, states + (k - 1) * DIGEST_LEN, merkle_path + 4 * k * DIGEST_LEN, states + k * DIGEST_LEN))

    # Last chunk -> root
    if height % 4 == 0:
        match_range(leaf_position_nibbles[div_ceil(height, 4) - 1], range(0, 16),
            lambda b: whir_do_4_merkle_levels(b, states + (div_ceil(height, 4) - 2) * DIGEST_LEN, merkle_path + 4 * (div_ceil(height, 4) - 1) * DIGEST_LEN, root))
    elif height % 4 == 1:
        match_range(leaf_position_nibbles[(height - height % 4) / 4], range(0, 16),
            lambda b: whir_do_1_merkle_level(b, states + (div_ceil(height, 4) - 2) * DIGEST_LEN, merkle_path + 4 * ((height - height % 4) / 4) * DIGEST_LEN, root))
    elif height % 4 == 2:
        match_range(leaf_position_nibbles[(height - height % 4) / 4], range(0, 16),
            lambda b: whir_do_2_merkle_levels(b, states + (div_ceil(height, 4) - 2) * DIGEST_LEN, merkle_path + 4 * ((height - height % 4) / 4) * DIGEST_LEN, root))
    elif height % 4 == 3:
        match_range(leaf_position_nibbles[(height - height % 4) / 4], range(0, 16),
            lambda b: whir_do_3_merkle_levels(b, states + (div_ceil(height, 4) - 2) * DIGEST_LEN, merkle_path + 4 * ((height - height % 4) / 4) * DIGEST_LEN, root))

    return leaf_data


@inline
def hash_and_verify_merkle_hint_with_initial_state(leaf_position_nibbles, root, height, num_chunks, initial_state, n_effective_chunks, n_effective_bits):
    # Hint and hash leaf (hint full data for dot product, but only hash effective chunks)
    leaf_data = Array(num_chunks * DIGEST_LEN)
    hint_merkle(leaf_data, num_chunks * DIGEST_LEN)
    leaf_hash = slice_hash_rtl_with_initial_state(initial_state, leaf_data, n_effective_chunks, n_effective_bits)

    # Hint and verify merkle path (processing 4 levels per nibble)
    merkle_path = Array(height * DIGEST_LEN)
    hint_merkle(merkle_path, height * DIGEST_LEN)

    states = Array((div_ceil(height, 4) - 1) * DIGEST_LEN)

    # First full nibble: leaf_hash -> states[0]
    match_range(leaf_position_nibbles[0], range(0, 16),
        lambda b: whir_do_4_merkle_levels(b, leaf_hash, merkle_path, states))

    # Middle nibble chunks: states[k-1] -> states[k]
    for k in unroll(1, div_ceil(height, 4) - 1):
        match_range(leaf_position_nibbles[k], range(0, 16),
            lambda b: whir_do_4_merkle_levels(b, states + (k - 1) * DIGEST_LEN, merkle_path + 4 * k * DIGEST_LEN, states + k * DIGEST_LEN))

    # Last chunk -> root
    if height % 4 == 0:
        match_range(leaf_position_nibbles[div_ceil(height, 4) - 1], range(0, 16),
            lambda b: whir_do_4_merkle_levels(b, states + (div_ceil(height, 4) - 2) * DIGEST_LEN, merkle_path + 4 * (div_ceil(height, 4) - 1) * DIGEST_LEN, root))
    elif height % 4 == 1:
        match_range(leaf_position_nibbles[(height - height % 4) / 4], range(0, 16),
            lambda b: whir_do_1_merkle_level(b, states + (div_ceil(height, 4) - 2) * DIGEST_LEN, merkle_path + 4 * ((height - height % 4) / 4) * DIGEST_LEN, root))
    elif height % 4 == 2:
        match_range(leaf_position_nibbles[(height - height % 4) / 4], range(0, 16),
            lambda b: whir_do_2_merkle_levels(b, states + (div_ceil(height, 4) - 2) * DIGEST_LEN, merkle_path + 4 * ((height - height % 4) / 4) * DIGEST_LEN, root))
    elif height % 4 == 3:
        match_range(leaf_position_nibbles[(height - height % 4) / 4], range(0, 16),
            lambda b: whir_do_3_merkle_levels(b, states + (div_ceil(height, 4) - 2) * DIGEST_LEN, merkle_path + 4 * ((height - height % 4) / 4) * DIGEST_LEN, root))

    return leaf_data


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
    # leaves_digests: pointer to a slice of n_paths pointers, each pointing to 1 chunk of 8 field elements
    # leave_positions: pointer to a slice of n_paths field elements (each < 2^height)
    # root: pointer to 1 chunk of 8 field elements
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
    for j in unroll(1, height):
        # Warning: this works only if leaf_position_bits[i] is known to be boolean:
        match leaf_position_bits[j]:
            case 0:
                poseidon16(
                    states + (j - 1) * DIGEST_LEN,
                    merkle_path + j * DIGEST_LEN,
                    states + j * DIGEST_LEN,
                )
            case 1:
                poseidon16(
                    merkle_path + j * DIGEST_LEN,
                    states + (j - 1) * DIGEST_LEN,
                    states + j * DIGEST_LEN,
                )
    copy_8(states + (height - 1) * DIGEST_LEN, root)
    return
