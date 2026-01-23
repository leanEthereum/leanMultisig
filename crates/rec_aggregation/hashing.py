from snark_lib import *

COMPRESSION = 1
PERMUTATION = 0

DIM = 5  # extension degree
VECTOR_LEN = 8

MERKLE_HEIGHTS_BASE = MERKLE_HEIGHTS_BASE_PLACEHOLDER
MERKLE_HEIGHTS_EXT = MERKLE_HEIGHTS_EXT_PLACEHOLDER
NUM_QUERIES_BASE = NUM_QUERIES_BASE_PLACEHOLDER
NUM_QUERIES_EXT = NUM_QUERIES_EXT_PLACEHOLDER
N_ROUNDS_BASE = len(NUM_QUERIES_BASE) - 1
N_ROUNDS_EXT = len(NUM_QUERIES_EXT) - 1


def batch_hash_slice(num_queries, all_data_to_hash, all_resulting_hashes, len):
    if len == DIM * 2:
        batch_hash_slice_const(num_queries, all_data_to_hash, all_resulting_hashes, DIM * 2)
        return
    if len == 16:
        batch_hash_slice_const(num_queries, all_data_to_hash, all_resulting_hashes, 16)
        return
    if len == 1:
        batch_hash_slice_const(num_queries, all_data_to_hash, all_resulting_hashes, 1)
        return
    assert False, "batch_hash_slice called with unsupported len"


def batch_hash_slice_const(num_queries, all_data_to_hash, all_resulting_hashes, len: Const):
    for i in range(0, num_queries):
        data = all_data_to_hash[i]
        res = slice_hash(ZERO_VEC_PTR, data, len)
        all_resulting_hashes[i] = res
    return


def slice_hash(seed, data, len: Const):
    states = Array(len * VECTOR_LEN)
    poseidon16(ZERO_VEC_PTR, data, states, COMPRESSION)
    state_indexes = Array(len)
    state_indexes[0] = states
    for j in unroll(1, len):
        state_indexes[j] = state_indexes[j - 1] + VECTOR_LEN
        poseidon16(state_indexes[j - 1], data + j * VECTOR_LEN, state_indexes[j], COMPRESSION)
    return state_indexes[len - 1]


def merkle_verif_batch(n_paths, merkle_paths, leaves_digests, leave_positions, root, height, num_queries):
    for i in unroll(0, N_ROUNDS_BASE + 1):
        if height + num_queries * 1000 == MERKLE_HEIGHTS_BASE[i] + NUM_QUERIES_BASE[i] * 1000:
            merkle_verif_batch_const(
                NUM_QUERIES_BASE[i],
                merkle_paths,
                leaves_digests,
                leave_positions,
                root,
                MERKLE_HEIGHTS_BASE[i],
            )
            return
    for i in unroll(0, N_ROUNDS_EXT + 1):
        if height + num_queries * 1000 == MERKLE_HEIGHTS_EXT[i] + NUM_QUERIES_EXT[i] * 1000:
            merkle_verif_batch_const(
                NUM_QUERIES_EXT[i],
                merkle_paths,
                leaves_digests,
                leave_positions,
                root,
                MERKLE_HEIGHTS_EXT[i],
            )
            return
    print(12345555)
    print(height)
    assert False


def merkle_verif_batch_const(n_paths: Const, merkle_paths, leaves_digests, leave_positions, root, height: Const):
    # n_paths: F
    # leaves_digests: pointer to a slice of n_paths vectorized pointers, each pointing to 1 chunk of 8 field elements
    # leave_positions: pointer to a slice of n_paths field elements (each < 2^height)
    # root: vectorized pointer to 1 chunk of 8 field elements
    # height: F

    for i in unroll(0, n_paths):
        merkle_verify(
            leaves_digests[i],
            merkle_paths + (i * height) * VECTOR_LEN,
            leave_positions[i],
            root,
            height,
        )

    return


def merkle_verify(leaf_digest, merkle_path, leaf_position_bits, root, height: Const):
    states = Array(height * VECTOR_LEN)

    # First merkle round
    match leaf_position_bits[0]:
        case 0:
            poseidon16(leaf_digest, merkle_path, states, COMPRESSION)
        case 1:
            poseidon16(merkle_path, leaf_digest, states, COMPRESSION)

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
                    COMPRESSION,
                )
            case 1:
                poseidon16(
                    merkle_path + j * VECTOR_LEN,
                    state_indexes[j - 1],
                    state_indexes[j],
                    COMPRESSION,
                )
    copy_8(state_indexes[height - 1], root)
    return
