from snark_lib import *

DIM = 5  # extension degree
DIGEST_LEN = 8

def batch_hash_slice(num_queries, all_data_to_hash, all_resulting_hashes, len):
    if len == DIM * 2:
        batch_hash_slice_const(num_queries, all_data_to_hash, all_resulting_hashes, DIM * 2)
        return
    if len == 16:
        batch_hash_slice_const(num_queries, all_data_to_hash, all_resulting_hashes, 16)
        return
    if len == 8:
        batch_hash_slice_const(num_queries, all_data_to_hash, all_resulting_hashes, 8)
        return
    if len == 20:
        batch_hash_slice_const(num_queries, all_data_to_hash, all_resulting_hashes, 20)
        return
    if len == 1:
        batch_hash_slice_const(num_queries, all_data_to_hash, all_resulting_hashes, 1)
        return
    if len == 4:
        batch_hash_slice_const(num_queries, all_data_to_hash, all_resulting_hashes, 4)
        return
    if len == 5:
        batch_hash_slice_const(num_queries, all_data_to_hash, all_resulting_hashes, 5)
        return
    print(len)
    assert False, "batch_hash_slice called with unsupported len"


def batch_hash_slice_const(num_queries, all_data_to_hash, all_resulting_hashes, len: Const):
    for i in range(0, num_queries):
        data = all_data_to_hash[i]
        res = slice_hash(data, len)
        all_resulting_hashes[i] = res
    return


@inline
def slice_hash(data, len):
    states = Array((len - 1) * DIGEST_LEN)
    poseidon16(data, data + DIGEST_LEN, states)
    state_indexes = Array(len)
    state_indexes[0] = states
    for j in unroll(1, len - 1):
        state_indexes[j] = state_indexes[j - 1] + DIGEST_LEN
        poseidon16(state_indexes[j - 1], data + (j + 1) * DIGEST_LEN, state_indexes[j])
    return state_indexes[len - 2]


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
