from snark_lib import *

DIM = 5  # extension degree
DIGEST_LEN = 8

# memory layout: [public_input (PUBLIC_INPUT_LEN)] [preamble_memory (PREAMBLE_MEMORY_LEN)] [runtime ...]
# `preamble_memory` is a region that is filled by the guest program, with usefull constants [0000...][1000...]...
PUBLIC_INPUT_LEN = DIGEST_LEN
ZERO_VEC_PTR = PUBLIC_INPUT_LEN
ZERO_VEC_LEN = ZERO_VEC_LEN_PLACEHOLDER
SAMPLING_DOMAIN_SEPARATOR_PTR = ZERO_VEC_PTR + ZERO_VEC_LEN
ONE_EF_PTR = SAMPLING_DOMAIN_SEPARATOR_PTR + DIGEST_LEN
NUM_REPEATED_ONES = NUM_REPEATED_ONES_PLACEHOLDER
REPEATED_ONES_PTR = ONE_EF_PTR + DIM
PREAMBLE_MEMORY_END = REPEATED_ONES_PTR + NUM_REPEATED_ONES
PREAMBLE_MEMORY_LEN = PREAMBLE_MEMORY_END - PUBLIC_INPUT_LEN

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

    poseidon16_compress(data + (num_chunks - 2) * DIGEST_LEN, data + (num_chunks - 1) * DIGEST_LEN, states)
    for j in unroll(1, num_chunks - 1):
        poseidon16_compress(states + (j - 1) * DIGEST_LEN, data + (num_chunks - 2 - j) * DIGEST_LEN, states + j * DIGEST_LEN)
    return states + (num_chunks - 2) * DIGEST_LEN


@inline
def slice_hash(data, num_chunks):
    states = Array((num_chunks - 1) * DIGEST_LEN)
    poseidon16_compress(data, data + DIGEST_LEN, states)
    for j in unroll(1, num_chunks - 1):
        poseidon16_compress(states + (j - 1) * DIGEST_LEN, data + (j + 1) * DIGEST_LEN, states + j * DIGEST_LEN)
    return states + (num_chunks - 2) * DIGEST_LEN

def slice_hash_with_iv_range(data, num_chunks, dest):
    debug_assert(0 < num_chunks)
    debug_assert(2 < num_chunks)
    states = Array((num_chunks - 1) * DIGEST_LEN)
    poseidon16_compress(ZERO_VEC_PTR, data, states)
    for j in range(1, num_chunks - 1):
        poseidon16_compress(states + (j - 1) * DIGEST_LEN, data + j * DIGEST_LEN, states + j * DIGEST_LEN)
    poseidon16_compress(states + (num_chunks - 2) * DIGEST_LEN, data + (num_chunks - 1) * DIGEST_LEN, dest)
    return

@inline
def slice_hash_with_iv(data, num_chunks, dest):
    debug_assert(2 <= num_chunks)
    states = Array(num_chunks * DIGEST_LEN)
    poseidon16_compress(ZERO_VEC_PTR, data, states)
    for j in unroll(1, num_chunks - 1):
        poseidon16_compress(states + (j - 1) * DIGEST_LEN, data + j * DIGEST_LEN, states + j * DIGEST_LEN)
    poseidon16_compress(states + (num_chunks - 2) * DIGEST_LEN, data + (num_chunks - 1) * DIGEST_LEN, dest)
    return


def slice_hash_with_iv_dynamic_unroll(data, num_chunks, num_chunks_bits: Const):
    debug_assert(num_chunks != 0)
    debug_assert(num_chunks < 2**num_chunks_bits)

    if num_chunks == 1:
        result = Array(DIGEST_LEN)
        poseidon16_compress(ZERO_VEC_PTR, data, result)
        return result

    states = Array(num_chunks * DIGEST_LEN)
    poseidon16_compress(ZERO_VEC_PTR, data, states)
    n_iters = num_chunks - 1
    state_ptr: Mut = states
    data_ptr: Mut = data + DIGEST_LEN
    for _ in dynamic_unroll(0, n_iters, num_chunks_bits):
        new_state = state_ptr + DIGEST_LEN
        poseidon16_compress(state_ptr, data_ptr, new_state)
        state_ptr = new_state
        data_ptr = data_ptr + DIGEST_LEN
    return state_ptr


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
        poseidon16_compress(state_in, path_chunk, temps)
    else:
        poseidon16_compress(path_chunk, state_in, temps)

    if b1 == 0:
        poseidon16_compress(temps, path_chunk + DIGEST_LEN, temps + DIGEST_LEN)
    else:
        poseidon16_compress(path_chunk + DIGEST_LEN, temps, temps + DIGEST_LEN)

    if b2 == 0:
        poseidon16_compress(temps + DIGEST_LEN, path_chunk + 2 * DIGEST_LEN, temps + 2 * DIGEST_LEN)
    else:
        poseidon16_compress(path_chunk + 2 * DIGEST_LEN, temps + DIGEST_LEN, temps + 2 * DIGEST_LEN)

    if b3 == 0:
        poseidon16_compress(temps + 2 * DIGEST_LEN, path_chunk + 3 * DIGEST_LEN, state_out)
    else:
        poseidon16_compress(path_chunk + 3 * DIGEST_LEN, temps + 2 * DIGEST_LEN, state_out)
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
        poseidon16_compress(state_in, path_chunk, temps)
    else:
        poseidon16_compress(path_chunk, state_in, temps)

    if b1 == 0:
        poseidon16_compress(temps, path_chunk + DIGEST_LEN, temps + DIGEST_LEN)
    else:
        poseidon16_compress(path_chunk + DIGEST_LEN, temps, temps + DIGEST_LEN)

    if b2 == 0:
        poseidon16_compress(temps + DIGEST_LEN, path_chunk + 2 * DIGEST_LEN, state_out)
    else:
        poseidon16_compress(path_chunk + 2 * DIGEST_LEN, temps + DIGEST_LEN, state_out)
    return


@inline
def whir_do_2_merkle_levels(b, state_in, path_chunk, state_out):
    b0 = b % 2
    r1 = (b - b0) / 2
    b1 = r1 % 2

    temp = Array(DIGEST_LEN)

    if b0 == 0:
        poseidon16_compress(state_in, path_chunk, temp)
    else:
        poseidon16_compress(path_chunk, state_in, temp)

    if b1 == 0:
        poseidon16_compress(temp, path_chunk + DIGEST_LEN, state_out)
    else:
        poseidon16_compress(path_chunk + DIGEST_LEN, temp, state_out)
    return


@inline
def whir_do_1_merkle_level(b, state_in, path_chunk, state_out):
    b0 = b % 2

    if b0 == 0:
        poseidon16_compress(state_in, path_chunk, state_out)
    else:
        poseidon16_compress(path_chunk, state_in, state_out)
    return


def merkle_verif_batch(merkle_paths, leaves_digests, leave_positions, root, height, num_queries):
    match_range(
        height,
        range(10, 26),
        lambda h: merkle_verif_batch_const(
            num_queries,
            merkle_paths,
            leaves_digests,
            leave_positions,
            root,
            h,
        ),
    )
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
            poseidon16_compress(leaf_digest, merkle_path, states)
        case 1:
            poseidon16_compress(merkle_path, leaf_digest, states)

    # Remaining merkle rounds
    for j in unroll(1, height):
        # Warning: this works only if leaf_position_bits[i] is known to be boolean:
        match leaf_position_bits[j]:
            case 0:
                poseidon16_compress(
                    states + (j - 1) * DIGEST_LEN,
                    merkle_path + j * DIGEST_LEN,
                    states + j * DIGEST_LEN,
                )
            case 1:
                poseidon16_compress(
                    merkle_path + j * DIGEST_LEN,
                    states + (j - 1) * DIGEST_LEN,
                    states + j * DIGEST_LEN,
                )
    copy_8(states + (height - 1) * DIGEST_LEN, root)
    return
