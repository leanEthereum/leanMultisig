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
    for i in range(0, n_paths):
        merkle_verify(
            leaves_digests[i],
            merkle_paths + (i * height) * DIGEST_LEN,
            leave_positions[i],
            root,
            height,
        )
    return


@inline
def do_4_merkle_levels(state_in, path_start, state_out, temp, v):
    bit0 = v % 2
    v1 = (v - bit0) / 2
    bit1 = v1 % 2
    v2 = (v1 - bit1) / 2
    bit2 = v2 % 2
    bit3 = (v2 - bit2) / 2
    s0 = temp
    s1 = temp + DIGEST_LEN
    s2 = temp + 2 * DIGEST_LEN
    if bit0 == 0:
        poseidon16(state_in, path_start, s0)
    if bit0 == 1:
        poseidon16(path_start, state_in, s0)
    if bit1 == 0:
        poseidon16(s0, path_start + DIGEST_LEN, s1)
    if bit1 == 1:
        poseidon16(path_start + DIGEST_LEN, s0, s1)
    if bit2 == 0:
        poseidon16(s1, path_start + 2 * DIGEST_LEN, s2)
    if bit2 == 1:
        poseidon16(path_start + 2 * DIGEST_LEN, s1, s2)
    if bit3 == 0:
        poseidon16(s2, path_start + 3 * DIGEST_LEN, state_out)
    if bit3 == 1:
        poseidon16(path_start + 3 * DIGEST_LEN, s2, state_out)
    return


@inline
def do_4_merkle_dispatch(state_in, path_start, state_out, temp, nibble):
    match_range(nibble, range(0, 16), lambda v: do_4_merkle_levels(state_in, path_start, state_out, temp, v))
    return


def _do_1_rem(state_in, path_start, state_out, v: Const):
    bit0 = v % 2
    if bit0 == 0:
        poseidon16(state_in, path_start, state_out)
    if bit0 == 1:
        poseidon16(path_start, state_in, state_out)
    return


def _do_2_rem(state_in, path_start, s0, state_out, v: Const):
    bit0 = v % 2
    bit1 = ((v - bit0) / 2) % 2
    if bit0 == 0:
        poseidon16(state_in, path_start, s0)
    if bit0 == 1:
        poseidon16(path_start, state_in, s0)
    if bit1 == 0:
        poseidon16(s0, path_start + DIGEST_LEN, state_out)
    if bit1 == 1:
        poseidon16(path_start + DIGEST_LEN, s0, state_out)
    return


def _do_3_rem(state_in, path_start, s0, s1, state_out, v: Const):
    bit0 = v % 2
    v1 = (v - bit0) / 2
    bit1 = v1 % 2
    bit2 = ((v1 - bit1) / 2) % 2
    if bit0 == 0:
        poseidon16(state_in, path_start, s0)
    if bit0 == 1:
        poseidon16(path_start, state_in, s0)
    if bit1 == 0:
        poseidon16(s0, path_start + DIGEST_LEN, s1)
    if bit1 == 1:
        poseidon16(path_start + DIGEST_LEN, s0, s1)
    if bit2 == 0:
        poseidon16(s1, path_start + 2 * DIGEST_LEN, state_out)
    if bit2 == 1:
        poseidon16(path_start + 2 * DIGEST_LEN, s1, state_out)
    return


def merkle_verify(leaf_digest, merkle_path, leaf_position_nibbles, root, height: Const):
    # Use correct integer division: (height - height%4) / 4
    remainder = height % 4
    n_full = (height - remainder) / 4

    # Pre-allocate all memory upfront (write-once friendly)
    states = Array(n_full * DIGEST_LEN)
    temps = Array(n_full * 3 * DIGEST_LEN)

    # First full nibble (uses leaf_digest as input)
    do_4_merkle_dispatch(leaf_digest, merkle_path, states, temps, leaf_position_nibbles[0])

    # Remaining full nibbles via runtime loop (body compiled once)
    for k in range(1, n_full):
        do_4_merkle_dispatch(states + (k - 1) * DIGEST_LEN, merkle_path + k * 4 * DIGEST_LEN, states + k * DIGEST_LEN, temps + k * 3 * DIGEST_LEN, leaf_position_nibbles[k])

    # Handle remainder levels and output to root
    # NOTE: nibble at n_full has 4 bits but only lower `remainder` bits matter.
    # We use match_range over full nibble range (0-16) and mask inside lambda.
    if remainder == 0:
        copy_8(states + (n_full - 1) * DIGEST_LEN, root)
    if remainder == 1:
        match_range(leaf_position_nibbles[n_full], range(0, 16), lambda v: _do_1_rem(states + (n_full - 1) * DIGEST_LEN, merkle_path + n_full * 4 * DIGEST_LEN, root, v))
    if remainder == 2:
        rem_temp = Array(DIGEST_LEN)
        match_range(leaf_position_nibbles[n_full], range(0, 16), lambda v: _do_2_rem(states + (n_full - 1) * DIGEST_LEN, merkle_path + n_full * 4 * DIGEST_LEN, rem_temp, root, v))
    if remainder == 3:
        rem_temps = Array(2 * DIGEST_LEN)
        rt0 = rem_temps
        rt1 = rem_temps + DIGEST_LEN
        match_range(leaf_position_nibbles[n_full], range(0, 16), lambda v: _do_3_rem(states + (n_full - 1) * DIGEST_LEN, merkle_path + n_full * 4 * DIGEST_LEN, rt0, rt1, root, v))

    return
