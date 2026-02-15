from snark_lib import *
from utils import *

V = V_PLACEHOLDER
V_GRINDING = V_GRINDING_PLACEHOLDER
W = W_PLACEHOLDER
CHAIN_LENGTH = 2 ** W
TARGET_SUM = TARGET_SUM_PLACEHOLDER
LOG_LIFETIME = LOG_LIFETIME_PLACEHOLDER
MESSAGE_LEN = MESSAGE_LEN_PLACEHOLDER
RANDOMNESS_LEN = RANDOMNESS_LEN_PLACEHOLDER
SIG_SIZE = RANDOMNESS_LEN + (V + LOG_LIFETIME) * DIM
NUM_ENCODING_FE = div_ceil((V + V_GRINDING), (24 / W))
MERKLE_LEVELS_PER_CHUNK = MERKLE_LEVELS_PER_CHUNK_PLACEHOLDER
N_MERKLE_CHUNKS = LOG_LIFETIME / MERKLE_LEVELS_PER_CHUNK

# Tweak table layout
TWEAK_LEN = 2
N_TWEAKS = 1 + V * CHAIN_LENGTH + (V - 1) + LOG_LIFETIME
TWEAK_TABLE_SIZE_FE = N_TWEAKS * TWEAK_LEN
TWEAK_ENCODING_OFFSET = 0
TWEAK_CHAIN_OFFSET = 1 * TWEAK_LEN
TWEAK_WOTS_PK_OFFSET = TWEAK_CHAIN_OFFSET + V * CHAIN_LENGTH * TWEAK_LEN
TWEAK_MERKLE_OFFSET = TWEAK_WOTS_PK_OFFSET + (V - 1) * TWEAK_LEN

# Buffer size for the hash-chaining trick: 3 prefix + DIGEST_LEN hash output.
# Hash output goes to buf + 3, then buf[0..3] is set to the prefix (pp or tweak).
# buf[0..8] = [prefix(3) | hash[0..5]] can then be used directly as the next hash input,
# avoiding a separate Array(DIGEST_LEN) allocation and copy_5.
BUF_SIZE = 3 + DIGEST_LEN


@inline
def build_left_fn(pp, data, out):
    out[0] = pp[0]
    out[1] = pp[1]
    out[2] = pp[2]
    copy_5(data, out + 3)
    return


@inline
def build_right_fn(tweak, data, out):
    out[0] = 0
    out[1] = tweak[0]
    out[2] = tweak[1]
    copy_5(data, out + 3)
    return


@inline
def build_right_chain_fn(tweak, out):
    # Chain hash: data is all zeros
    out[0] = 0
    out[1] = tweak[0]
    out[2] = tweak[1]
    copy_5(ZERO_VEC_PTR, out + 3)
    return


@inline
def xmss_verify(pub_key, message, signature, tweak_table, merkle_chunks):
    # pub_key: 8 FE = merkle_root(DIM) | public_param(3)
    # signature: randomness(RANDOMNESS_LEN) | chain_tips(V * DIM) | merkle_path(LOG_LIFETIME * DIM)

    public_param = pub_key + DIM
    randomness = signature
    chain_starts = signature + RANDOMNESS_LEN
    merkle_path = chain_starts + V * DIM

    # 1) Encode: poseidon16(message[0:8], [msg[8] | randomness(5) | tweak_encoding(2)])
    #            poseidon16(pre_compressed, pub_key_flat)
    encoding_tweak = tweak_table + TWEAK_ENCODING_OFFSET
    a_input_right = Array(DIGEST_LEN)
    a_input_right[0] = message[DIGEST_LEN]
    copy_5(randomness, a_input_right + 1)
    a_input_right[1 + RANDOMNESS_LEN] = encoding_tweak[0]
    a_input_right[1 + RANDOMNESS_LEN + 1] = encoding_tweak[1]
    pre_compressed = Array(DIGEST_LEN)
    poseidon16(message, a_input_right, pre_compressed)

    encoding_fe = Array(DIGEST_LEN)
    poseidon16(pre_compressed, pub_key, encoding_fe)

    encoding = Array(NUM_ENCODING_FE * 24 / W)
    remaining = Array(NUM_ENCODING_FE)

    # TODO: decompose by chunks of 2.w bits (or even 3.w bits) and use a big match on the w^2 (or w^3) possibilities
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

    # 2) Chain hashes -> recover WOTS public key
    wots_public_key = Array(V * DIGEST_LEN)

    for i in unroll(0, V):
        num_hashes = (CHAIN_LENGTH - 1) - encoding[i]
        chain_start = chain_starts + i * DIM
        chain_end = wots_public_key + i * DIGEST_LEN
        chain_i_tweaks = tweak_table + TWEAK_CHAIN_OFFSET + i * CHAIN_LENGTH * TWEAK_LEN
        match_range(num_hashes,
                    range(0, 1), lambda _: copy_5(chain_start, chain_end),
                    range(1, CHAIN_LENGTH), lambda n: chain_hash(chain_start, n, chain_end, public_param, chain_i_tweaks))

    # 3) Hash WOTS public key
    wots_pk_tweaks = tweak_table + TWEAK_WOTS_PK_OFFSET
    expected_leaf = wots_pk_hash(wots_public_key, public_param, wots_pk_tweaks)

    # 4) Merkle verification
    merkle_tweaks = tweak_table + TWEAK_MERKLE_OFFSET
    xmss_merkle_verify(expected_leaf, merkle_path, merkle_chunks, pub_key, public_param, merkle_tweaks)
    return


def chain_hash(input, n: Const, output, public_param, chain_i_tweaks):
    starting_step = CHAIN_LENGTH - 1 - n

    # First hash: build left and right from scratch (no prior hash output to reuse)
    left_first = Array(DIGEST_LEN)
    build_left_fn(public_param, input, left_first)
    right_first = Array(DIGEST_LEN)
    build_right_chain_fn(chain_i_tweaks + starting_step * TWEAK_LEN, right_first)

    if n == 1:
        poseidon16(left_first, right_first, output)
        return

    # Buffer trick: hash output goes to buf + 3, then pp is prepended at buf[0..3].
    # buf[0..8] = [pp(3) | hash[0..5]] serves directly as the left input for the next hash,
    # avoiding a separate Array + copy_5 per step.
    bufs = Array((n - 1) * BUF_SIZE)
    buf_indexes = Array(n - 1)
    buf_indexes[0] = bufs

    poseidon16(left_first, right_first, bufs + 3)
    bufs[0] = public_param[0]
    bufs[1] = public_param[1]
    bufs[2] = public_param[2]

    for j in unroll(1, n - 1):
        buf_indexes[j] = buf_indexes[j - 1] + BUF_SIZE
        cur_buf = buf_indexes[j]
        right_j = Array(DIGEST_LEN)
        build_right_chain_fn(chain_i_tweaks + (starting_step + j) * TWEAK_LEN, right_j)
        poseidon16(buf_indexes[j - 1], right_j, cur_buf + 3)
        cur_buf[0] = public_param[0]
        cur_buf[1] = public_param[1]
        cur_buf[2] = public_param[2]

    # Final hash: last buf is already a valid left input
    right_last = Array(DIGEST_LEN)
    build_right_chain_fn(chain_i_tweaks + (starting_step + n - 1) * TWEAK_LEN, right_last)
    poseidon16(buf_indexes[n - 2], right_last, output)
    return


def wots_pk_hash(wots_public_key, public_param, wots_pk_tweaks):
    # Sequential hash over V elements at DIGEST_LEN stride
    # poseidon16(build_left(pp, wots[0]), build_right(tweak[0], wots[1])) -> h
    # poseidon16([pp | h], build_right(tweak[i], wots[i+1])) for i=1..V-2
    # Final: poseidon16([pp | h], build_right(tweak[V-2], wots[V-1]))

    # First hash: build from scratch
    left0 = Array(DIGEST_LEN)
    build_left_fn(public_param, wots_public_key, left0)
    right0 = Array(DIGEST_LEN)
    build_right_fn(wots_pk_tweaks, wots_public_key + DIGEST_LEN, right0)

    # Buffer trick for intermediate states
    bufs = Array((V - 2) * BUF_SIZE)
    buf_indexes = Array(V - 2)
    buf_indexes[0] = bufs

    poseidon16(left0, right0, bufs + 3)
    bufs[0] = public_param[0]
    bufs[1] = public_param[1]
    bufs[2] = public_param[2]

    for i in unroll(1, V - 2):
        buf_indexes[i] = buf_indexes[i - 1] + BUF_SIZE
        cur_buf = buf_indexes[i]
        right_i = Array(DIGEST_LEN)
        build_right_fn(wots_pk_tweaks + i * TWEAK_LEN, wots_public_key + (i + 1) * DIGEST_LEN, right_i)
        poseidon16(buf_indexes[i - 1], right_i, cur_buf + 3)
        cur_buf[0] = public_param[0]
        cur_buf[1] = public_param[1]
        cur_buf[2] = public_param[2]

    # Final hash
    result = Array(DIGEST_LEN)
    right_last = Array(DIGEST_LEN)
    build_right_fn(wots_pk_tweaks + (V - 2) * TWEAK_LEN, wots_public_key + (V - 1) * DIGEST_LEN, right_last)
    poseidon16(buf_indexes[V - 3], right_last, result)

    return result


@inline
def do_4_merkle_levels(b, state_in, path_chunk, state_out, public_param, merkle_tweaks_chunk):
    # b encodes 4 is_left bits; path elements at DIM stride
    b0 = b % 2
    r1 = (b - b0) / 2
    b1 = r1 % 2
    r2 = (r1 - b1) / 2
    b2 = r2 % 2
    r3 = (r2 - b2) / 2
    b3 = r3 % 2

    # Level 0: build from external state_in and path_chunk (no prior hash to reuse)
    left0 = Array(DIGEST_LEN)
    right0 = Array(DIGEST_LEN)
    if b0 == 1:
        build_left_fn(public_param, state_in, left0)
        build_right_fn(merkle_tweaks_chunk, path_chunk, right0)
    else:
        build_left_fn(public_param, path_chunk, left0)
        build_right_fn(merkle_tweaks_chunk, state_in, right0)

    # Buffer trick: hash output to buf + 3, then prepend prefix.
    # If state goes left: buf = [pp | hash[0..5]], used as left input.
    # If state goes right: buf = [0, tw0, tw1 | hash[0..5]], used as right input.
    buf0 = Array(BUF_SIZE)
    poseidon16(left0, right0, buf0 + 3)

    # Level 1
    other1 = Array(DIGEST_LEN)
    buf1 = Array(BUF_SIZE)
    if b1 == 1:
        buf0[0] = public_param[0]
        buf0[1] = public_param[1]
        buf0[2] = public_param[2]
        build_right_fn(merkle_tweaks_chunk + 1 * TWEAK_LEN, path_chunk + 1 * DIM, other1)
        poseidon16(buf0, other1, buf1 + 3)
    else:
        buf0[0] = 0
        buf0[1] = merkle_tweaks_chunk[1 * TWEAK_LEN]
        buf0[2] = merkle_tweaks_chunk[1 * TWEAK_LEN + 1]
        build_left_fn(public_param, path_chunk + 1 * DIM, other1)
        poseidon16(other1, buf0, buf1 + 3)

    # Level 2
    other2 = Array(DIGEST_LEN)
    buf2 = Array(BUF_SIZE)
    if b2 == 1:
        buf1[0] = public_param[0]
        buf1[1] = public_param[1]
        buf1[2] = public_param[2]
        build_right_fn(merkle_tweaks_chunk + 2 * TWEAK_LEN, path_chunk + 2 * DIM, other2)
        poseidon16(buf1, other2, buf2 + 3)
    else:
        buf1[0] = 0
        buf1[1] = merkle_tweaks_chunk[2 * TWEAK_LEN]
        buf1[2] = merkle_tweaks_chunk[2 * TWEAK_LEN + 1]
        build_left_fn(public_param, path_chunk + 2 * DIM, other2)
        poseidon16(other2, buf1, buf2 + 3)

    # Level 3 -> state_out
    other3 = Array(DIGEST_LEN)
    if b3 == 1:
        buf2[0] = public_param[0]
        buf2[1] = public_param[1]
        buf2[2] = public_param[2]
        build_right_fn(merkle_tweaks_chunk + 3 * TWEAK_LEN, path_chunk + 3 * DIM, other3)
        poseidon16(buf2, other3, state_out)
    else:
        buf2[0] = 0
        buf2[1] = merkle_tweaks_chunk[3 * TWEAK_LEN]
        buf2[2] = merkle_tweaks_chunk[3 * TWEAK_LEN + 1]
        build_left_fn(public_param, path_chunk + 3 * DIM, other3)
        poseidon16(other3, buf2, state_out)
    return


@inline
def xmss_merkle_verify(leaf_digest, merkle_path, merkle_chunks, expected_root, public_param, merkle_tweaks):
    states = Array((N_MERKLE_CHUNKS - 1) * DIGEST_LEN)

    # First chunk
    match_range(merkle_chunks[0], range(0, 16), lambda b: do_4_merkle_levels(
        b, leaf_digest, merkle_path, states, public_param, merkle_tweaks))

    state_indexes = Array(N_MERKLE_CHUNKS - 1)
    state_indexes[0] = states
    for j in unroll(1, N_MERKLE_CHUNKS - 1):
        state_indexes[j] = state_indexes[j - 1] + DIGEST_LEN
        match_range(merkle_chunks[j], range(0, 16), lambda b: do_4_merkle_levels(
            b, state_indexes[j - 1],
            merkle_path + j * MERKLE_LEVELS_PER_CHUNK * DIM,
            state_indexes[j],
            public_param,
            merkle_tweaks + j * MERKLE_LEVELS_PER_CHUNK * TWEAK_LEN))

    # Last chunk: write to temp, then assert match with expected_root (write-once)
    last_output = Array(DIGEST_LEN)
    match_range(merkle_chunks[N_MERKLE_CHUNKS - 1], range(0, 16), lambda b: do_4_merkle_levels(
        b, state_indexes[N_MERKLE_CHUNKS - 2],
        merkle_path + (N_MERKLE_CHUNKS - 1) * MERKLE_LEVELS_PER_CHUNK * DIM,
        last_output,
        public_param,
        merkle_tweaks + (N_MERKLE_CHUNKS - 1) * MERKLE_LEVELS_PER_CHUNK * TWEAK_LEN))

    # Assert computed root == expected (first DIM elements)
    copy_5(last_output, expected_root)
    return
