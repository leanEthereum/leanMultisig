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


def slice_hash_rtl(data, num_chunks):
    """RATE=12 sponge over data of length num_chunks * 8 base elements.
    Pads internally so that the absorbed length is 16 + 12*k (sponge-aligned),
    matching the native prover's padded_full_base_width helper.

    `num_chunks` is `Const`, so all arithmetic and the if-branches below
    resolve at compile time.

    Algorithm (mirrors Rust hash_rtl_iter for RATE=12, WIDTH=16):
      state = padded_data[L-16..L]  # initial state from last 16 elements
      compress(state)
      for chunk_idx descending from k-1 to 0:
          state[0..4] persists (capacity)
          state[4..16] = padded_data[chunk_idx*12..(chunk_idx+1)*12]
          compress(state)
      return state[0..8]
    """
    if num_chunks == 1:
        # data_len = 8 ; pad to 16 ; one permute.
        buf = Array(16)
        for i in unroll(0, 8):
            buf[i] = data[i]
        for i in unroll(8, 16):
            buf[i] = 0
        result = Array(DIGEST_LEN)
        poseidon16_compress(buf, buf + DIGEST_LEN, result)
        return result
    if num_chunks == 4:
        return slice_hash_rtl_rate12(data, 32, 40, 2)
    if num_chunks == 5:
        return slice_hash_rtl_rate12(data, 40, 40, 2)
    if num_chunks == 8:
        return slice_hash_rtl_rate12(data, 64, 64, 4)
    if num_chunks == 10:
        return slice_hash_rtl_rate12(data, 80, 88, 6)
    if num_chunks == 16:
        return slice_hash_rtl_rate12(data, 128, 136, 10)
    if num_chunks == 20:
        return slice_hash_rtl_rate12(data, 160, 160, 12)
    print(num_chunks)
    assert False, "slice_hash_rtl called with unsupported num_chunks"


def slice_hash_rtl_rate12(data, data_len: Const, padded_len: Const, n_chunks_12: Const):
    """Internal helper for RATE=12 sponge with explicit padding params.
    Pre: padded_len = 16 + n_chunks_12 * 12 ; padded_len >= data_len.
    """
    if padded_len == data_len:
        # No padding needed; absorb directly from data.
        return slice_hash_rtl_rate12_no_pad(data, padded_len, n_chunks_12)
    # Build a local padded buffer once, then absorb from it.
    padded_data = Array(padded_len)
    for i in unroll(0, data_len):
        padded_data[i] = data[i]
    for i in unroll(data_len, padded_len):
        padded_data[i] = 0
    return slice_hash_rtl_rate12_no_pad(padded_data, padded_len, n_chunks_12)


def slice_hash_rtl_rate12_no_pad(padded_data, padded_len: Const, n_chunks_12: Const):
    """MMO sponge: ADD message into rate, full-state feedforward.

    The chaining variable is the FULL 16-element state across rounds, giving
    output_bits/2 = 124-bit collision security regardless of capacity.
    The output is the first 8 elements of the final 16-element state.

    states[k*16..(k+1)*16] holds the full 16-element state after round k.
    """
    states = Array((n_chunks_12 + 1) * 16)

    # Round 0: states[0..16] = padded_data[len-16..len] + perm(padded_data[len-16..len])
    # (zero IV implicit; first absorb feeds the last 16 elements of input as the initial state).
    poseidon16_permute(
        padded_data + padded_len - 16,
        padded_data + padded_len - 8,
        states,
    )

    # Subsequent rounds: absorb 12-element chunks RTL using MMO compression.
    #   pre[0..4]   = states[j*16..j*16+4]            (capacity unchanged)
    #   pre[4..16]  = states[j*16+4..j*16+16] + chunk (rate gets ADDED with chunk)
    #   states[(j+1)*16..(j+2)*16] = pre + perm(pre)  (full-state feedforward)
    for j in unroll(0, n_chunks_12):
        chunk_idx = n_chunks_12 - 1 - j

        pre = Array(16)
        for k in unroll(0, 4):
            pre[k] = states[j * 16 + k]
        for k in unroll(0, 12):
            pre[4 + k] = states[j * 16 + 4 + k] + padded_data[chunk_idx * 12 + k]

        poseidon16_permute(pre, pre + 8, states + (j + 1) * 16)

    # Output the first 8 elements of the final state.
    return states + n_chunks_12 * 16


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
