from snark_lib import *
from utils import *

V = V_PLACEHOLDER
V_GRINDING = V_GRINDING_PLACEHOLDER
W = W_PLACEHOLDER
CHAIN_LENGTH = 2**W
TARGET_SUM = TARGET_SUM_PLACEHOLDER
LOG_LIFETIME = LOG_LIFETIME_PLACEHOLDER
MESSAGE_LEN = MESSAGE_LEN_PLACEHOLDER
RANDOMNESS_LEN = RANDOMNESS_LEN_PLACEHOLDER
PUBLIC_PARAM_LEN_FE = PUBLIC_PARAM_LEN_FE_PLACEHOLDER
XMSS_DIGEST = XMSS_DIGEST_SIZE_PLACEHOLDER
PUB_KEY_SIZE = XMSS_DIGEST + PUBLIC_PARAM_LEN_FE
PP_IN_LEFT = DIGEST_LEN - XMSS_DIGEST
SIG_SIZE = RANDOMNESS_LEN + (V + LOG_LIFETIME) * XMSS_DIGEST
NUM_ENCODING_FE = div_ceil((V + V_GRINDING), (24 / W))
MERKLE_LEVELS_PER_CHUNK = MERKLE_LEVELS_PER_CHUNK_PLACEHOLDER
N_MERKLE_CHUNKS = LOG_LIFETIME / MERKLE_LEVELS_PER_CHUNK

# Tweak table layout
TWEAK_LEN = 2
N_TWEAKS = 1 + V * CHAIN_LENGTH + (V - 1) + LOG_LIFETIME
TWEAK_TABLE_SIZE_FE_PADDED = next_multiple_of(N_TWEAKS * TWEAK_LEN, DIGEST_LEN)
TWEAK_ENCODING_OFFSET = 0
TWEAK_CHAIN_OFFSET = 1 * TWEAK_LEN
TWEAK_WOTS_PK_OFFSET = TWEAK_CHAIN_OFFSET + V * CHAIN_LENGTH * TWEAK_LEN
TWEAK_MERKLE_OFFSET = TWEAK_WOTS_PK_OFFSET + (V - 1) * TWEAK_LEN

# Buffer size for the hash-chaining trick: PP_IN_LEFT prefix + DIGEST_LEN hash output.
# Hash output goes to buf + PP_IN_LEFT, then buf[0..PP_IN_LEFT] is set to the prefix.
# buf[0..8] = [prefix(PP_IN_LEFT) | hash[0..XMSS_DIGEST]] is a valid left input.
BUF_SIZE = PP_IN_LEFT + DIGEST_LEN


@inline
def build_left_fn(pp, data, out):
    for k in unroll(0, PP_IN_LEFT):
        out[k] = pp[k]
    for k in unroll(0, XMSS_DIGEST):
        out[PP_IN_LEFT + k] = data[k]
    return


@inline
def build_right_fn(tweak, data, out):
    # [tweak(2) | zeros(2) | data(XMSS_DIGEST)]
    out[0] = tweak[0]
    out[1] = tweak[1]
    out[2] = 0
    out[3] = 0
    for k in unroll(0, XMSS_DIGEST):
        out[4 + k] = data[k]
    return


@inline
def build_right_chain_fn(tweak, out):
    # Chain hash: data is all zeros. [tweak(2) | zeros(6)]
    out[0] = tweak[0]
    out[1] = tweak[1]
    for k in unroll(2, DIGEST_LEN):
        out[k] = 0
    return


@inline
def xmss_verify(pub_key, message, signature, tweak_table, merkle_chunks):
    # pub_key: PUB_KEY_SIZE FE = merkle_root(XMSS_DIGEST) | public_param(PUBLIC_PARAM_LEN_FE)
    # signature: randomness(RANDOMNESS_LEN) | chain_tips(V * XMSS_DIGEST) | merkle_path(LOG_LIFETIME * XMSS_DIGEST)

    public_param = pub_key + XMSS_DIGEST
    randomness = signature
    chain_starts = signature + RANDOMNESS_LEN
    merkle_path = chain_starts + V * XMSS_DIGEST

    # 1) Encode: poseidon16_compress(message[0:8], [msg[8] | randomness(5) | tweak_encoding(2)])
    #            poseidon16_compress(pre_compressed, [pp(4) | zeros(4)])
    encoding_tweak = tweak_table + TWEAK_ENCODING_OFFSET
    a_input_right = Array(DIGEST_LEN)
    a_input_right[0] = message[DIGEST_LEN]
    copy_5(randomness, a_input_right + 1)
    a_input_right[1 + RANDOMNESS_LEN] = encoding_tweak[0]
    a_input_right[1 + RANDOMNESS_LEN + 1] = encoding_tweak[1]
    pre_compressed = Array(DIGEST_LEN)
    poseidon16_compress(message, a_input_right, pre_compressed)

    pp_input = Array(DIGEST_LEN)
    for k in unroll(0, PUBLIC_PARAM_LEN_FE):
        pp_input[k] = public_param[k]
    for k in unroll(PUBLIC_PARAM_LEN_FE, DIGEST_LEN):
        pp_input[k] = 0
    encoding_fe = Array(DIGEST_LEN)
    poseidon16_compress(pre_compressed, pp_input, encoding_fe)

    encoding = Array(NUM_ENCODING_FE * 24 / W)
    remaining = Array(NUM_ENCODING_FE)

    # TODO: decompose by chunks of 2.w bits (or even 3.w bits) and use a big match on the w^2 (or w^3) possibilities
    hint_decompose_bits_xmss(encoding, remaining, encoding_fe, NUM_ENCODING_FE, W)

    # check that the decomposition is correct
    for i in unroll(0, NUM_ENCODING_FE):
        for j in unroll(0, 24 / W):
            assert encoding[i * (24 / W) + j] < CHAIN_LENGTH

        assert remaining[i] < 2**7 - 1

        partial_sum: Mut = remaining[i] * 2**24
        for j in unroll(0, 24 / W):
            partial_sum += encoding[i * (24 / W) + j] * CHAIN_LENGTH**j
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
    MAX_CHAIN_HASHES = CHAIN_LENGTH - 1

    for i in unroll(0, V):
        num_hashes = (CHAIN_LENGTH - 1) - encoding[i]
        chain_start = chain_starts + i * XMSS_DIGEST
        chain_end = wots_public_key + i * DIGEST_LEN
        chain_i_tweaks = tweak_table + TWEAK_CHAIN_OFFSET + i * CHAIN_LENGTH * TWEAK_LEN

        # Pre-allocate all buffers (constant allocation regardless of num_hashes)
        ch_left = Array(DIGEST_LEN)
        ch_right = Array(DIGEST_LEN)
        ch_bufs = Array((MAX_CHAIN_HASHES - 1) * BUF_SIZE)
        ch_buf_idx = Array(MAX_CHAIN_HASHES - 1)
        ch_rights = Array((MAX_CHAIN_HASHES - 1) * DIGEST_LEN)
        ch_right_last = Array(DIGEST_LEN)

        match_range(
            num_hashes,
            range(0, 1),
            lambda _: copy_xmss_digest(chain_start, chain_end),
            range(1, CHAIN_LENGTH),
            lambda n: chain_hash_pa(chain_start, n, chain_end, public_param, chain_i_tweaks, ch_left, ch_right, ch_bufs, ch_buf_idx, ch_rights, ch_right_last),
        )

    # 3) Hash WOTS public key
    wots_pk_tweaks = tweak_table + TWEAK_WOTS_PK_OFFSET
    expected_leaf = wots_pk_hash(wots_public_key, public_param, wots_pk_tweaks)

    # 4) Merkle verification
    merkle_tweaks = tweak_table + TWEAK_MERKLE_OFFSET
    xmss_merkle_verify(expected_leaf, merkle_path, merkle_chunks, pub_key, public_param, merkle_tweaks)
    return


@inline
def copy_xmss_digest(src, dst):
    # Copy XMSS_DIGEST elements from src to dst (within a DIGEST_LEN-strided destination)
    for k in unroll(0, XMSS_DIGEST):
        dst[k] = src[k]
    return


@inline
def chain_hash_pa(input, n, output, public_param, chain_i_tweaks, ch_left, ch_right, ch_bufs, ch_buf_idx, ch_rights, ch_right_last):
    # Uses pre-allocated buffers (zero internal allocation for parallel_range compatibility)
    starting_step = CHAIN_LENGTH - 1 - n

    # First hash: build left and right from scratch
    build_left_fn(public_param, input, ch_left)
    build_right_chain_fn(chain_i_tweaks + starting_step * TWEAK_LEN, ch_right)

    if n == 1:
        poseidon16_compress(ch_left, ch_right, output)
    else:
        # Buffer trick: hash output goes to buf + PP_IN_LEFT, then pp is prepended.
        ch_buf_idx[0] = ch_bufs
        poseidon16_compress(ch_left, ch_right, ch_bufs + PP_IN_LEFT)
        for k in unroll(0, PP_IN_LEFT):
            ch_bufs[k] = public_param[k]

        for j in unroll(1, n - 1):
            ch_buf_idx[j] = ch_buf_idx[j - 1] + BUF_SIZE
            cur_buf = ch_buf_idx[j]
            right_j = ch_rights + (j - 1) * DIGEST_LEN
            build_right_chain_fn(chain_i_tweaks + (starting_step + j) * TWEAK_LEN, right_j)
            poseidon16_compress(ch_buf_idx[j - 1], right_j, cur_buf + PP_IN_LEFT)
            for k in unroll(0, PP_IN_LEFT):
                cur_buf[k] = public_param[k]

        # Final hash
        build_right_chain_fn(chain_i_tweaks + (starting_step + n - 1) * TWEAK_LEN, ch_right_last)
        poseidon16_compress(ch_buf_idx[n - 2], ch_right_last, output)
    return


def wots_pk_hash(wots_public_key, public_param, wots_pk_tweaks):
    # Sequential hash over V elements at DIGEST_LEN stride

    # First hash: build from scratch
    left0 = Array(DIGEST_LEN)
    build_left_fn(public_param, wots_public_key, left0)
    right0 = Array(DIGEST_LEN)
    build_right_fn(wots_pk_tweaks, wots_public_key + DIGEST_LEN, right0)

    # Buffer trick for intermediate states
    bufs = Array((V - 2) * BUF_SIZE)
    buf_indexes = Array(V - 2)
    buf_indexes[0] = bufs

    poseidon16_compress(left0, right0, bufs + PP_IN_LEFT)
    for k in unroll(0, PP_IN_LEFT):
        bufs[k] = public_param[k]

    for i in unroll(1, V - 2):
        buf_indexes[i] = buf_indexes[i - 1] + BUF_SIZE
        cur_buf = buf_indexes[i]
        right_i = Array(DIGEST_LEN)
        build_right_fn(wots_pk_tweaks + i * TWEAK_LEN, wots_public_key + (i + 1) * DIGEST_LEN, right_i)
        poseidon16_compress(buf_indexes[i - 1], right_i, cur_buf + PP_IN_LEFT)
        for k in unroll(0, PP_IN_LEFT):
            cur_buf[k] = public_param[k]

    # Final hash
    result = Array(DIGEST_LEN)
    right_last = Array(DIGEST_LEN)
    build_right_fn(wots_pk_tweaks + (V - 2) * TWEAK_LEN, wots_public_key + (V - 1) * DIGEST_LEN, right_last)
    poseidon16_compress(buf_indexes[V - 3], right_last, result)

    return result


@inline
def set_buf_prefix_left(buf, public_param):
    for k in unroll(0, PP_IN_LEFT):
        buf[k] = public_param[k]
    return


@inline
def set_buf_prefix_right(buf, tweak):
    buf[0] = tweak[0]
    buf[1] = tweak[1]
    buf[2] = 0
    buf[3] = 0
    return


@inline
def do_4_merkle_levels(b, state_in, path_chunk, state_out, public_param, merkle_tweaks_chunk):
    # b encodes 4 is_left bits; path elements at XMSS_DIGEST stride
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

    # Buffer trick: hash output to buf + PP_IN_LEFT, then prepend prefix.
    buf0 = Array(BUF_SIZE)
    poseidon16_compress(left0, right0, buf0 + PP_IN_LEFT)

    # Level 1
    other1 = Array(DIGEST_LEN)
    buf1 = Array(BUF_SIZE)
    if b1 == 1:
        set_buf_prefix_left(buf0, public_param)
        build_right_fn(merkle_tweaks_chunk + 1 * TWEAK_LEN, path_chunk + 1 * XMSS_DIGEST, other1)
        poseidon16_compress(buf0, other1, buf1 + PP_IN_LEFT)
    else:
        set_buf_prefix_right(buf0, merkle_tweaks_chunk + 1 * TWEAK_LEN)
        build_left_fn(public_param, path_chunk + 1 * XMSS_DIGEST, other1)
        poseidon16_compress(other1, buf0, buf1 + PP_IN_LEFT)

    # Level 2
    other2 = Array(DIGEST_LEN)
    buf2 = Array(BUF_SIZE)
    if b2 == 1:
        set_buf_prefix_left(buf1, public_param)
        build_right_fn(merkle_tweaks_chunk + 2 * TWEAK_LEN, path_chunk + 2 * XMSS_DIGEST, other2)
        poseidon16_compress(buf1, other2, buf2 + PP_IN_LEFT)
    else:
        set_buf_prefix_right(buf1, merkle_tweaks_chunk + 2 * TWEAK_LEN)
        build_left_fn(public_param, path_chunk + 2 * XMSS_DIGEST, other2)
        poseidon16_compress(other2, buf1, buf2 + PP_IN_LEFT)

    # Level 3 -> state_out
    other3 = Array(DIGEST_LEN)
    if b3 == 1:
        set_buf_prefix_left(buf2, public_param)
        build_right_fn(merkle_tweaks_chunk + 3 * TWEAK_LEN, path_chunk + 3 * XMSS_DIGEST, other3)
        poseidon16_compress(buf2, other3, state_out)
    else:
        set_buf_prefix_right(buf2, merkle_tweaks_chunk + 3 * TWEAK_LEN)
        build_left_fn(public_param, path_chunk + 3 * XMSS_DIGEST, other3)
        poseidon16_compress(other3, buf2, state_out)
    return


@inline
def xmss_merkle_verify(leaf_digest, merkle_path, merkle_chunks, expected_root, public_param, merkle_tweaks):
    states = Array((N_MERKLE_CHUNKS - 1) * DIGEST_LEN)

    # First chunk
    match_range(merkle_chunks[0], range(0, 16), lambda b: do_4_merkle_levels(b, leaf_digest, merkle_path, states, public_param, merkle_tweaks))

    state_indexes = Array(N_MERKLE_CHUNKS - 1)
    state_indexes[0] = states
    for j in unroll(1, N_MERKLE_CHUNKS - 1):
        state_indexes[j] = state_indexes[j - 1] + DIGEST_LEN
        match_range(
            merkle_chunks[j],
            range(0, 16),
            lambda b: do_4_merkle_levels(
                b,
                state_indexes[j - 1],
                merkle_path + j * MERKLE_LEVELS_PER_CHUNK * XMSS_DIGEST,
                state_indexes[j],
                public_param,
                merkle_tweaks + j * MERKLE_LEVELS_PER_CHUNK * TWEAK_LEN,
            ),
        )

    # Last chunk: write to temp, then assert match with expected_root (write-once)
    last_output = Array(DIGEST_LEN)
    match_range(
        merkle_chunks[N_MERKLE_CHUNKS - 1],
        range(0, 16),
        lambda b: do_4_merkle_levels(
            b,
            state_indexes[N_MERKLE_CHUNKS - 2],
            merkle_path + (N_MERKLE_CHUNKS - 1) * MERKLE_LEVELS_PER_CHUNK * XMSS_DIGEST,
            last_output,
            public_param,
            merkle_tweaks + (N_MERKLE_CHUNKS - 1) * MERKLE_LEVELS_PER_CHUNK * TWEAK_LEN,
        ),
    )

    # Assert computed root == expected (first XMSS_DIGEST elements)
    copy_xmss_digest(last_output, expected_root)
    return
