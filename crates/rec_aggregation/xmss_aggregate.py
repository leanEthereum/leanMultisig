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

# Tweak table layout: each tweak is stored as a 4-FE slot [tw[0], tw[1], 0, 0].
# Pointers point directly to tw[0]. Individual access: ptr[0] = tw[0], ptr[1] = tw[1].
# Compatible with memcopy_4 (stride_in=4).
TWEAK_LEN = 4  # stride / slot size in the padded table
N_TWEAKS = 1 + V * CHAIN_LENGTH + (V - 1) + LOG_LIFETIME
TWEAK_TABLE_SIZE_FE_PADDED = next_multiple_of(N_TWEAKS * TWEAK_LEN, DIGEST_LEN)
TWEAK_ENCODING_OFFSET = 0
TWEAK_CHAIN_OFFSET = TWEAK_ENCODING_OFFSET + TWEAK_LEN
TWEAK_WOTS_PK_OFFSET = TWEAK_CHAIN_OFFSET + V * CHAIN_LENGTH * TWEAK_LEN
TWEAK_MERKLE_OFFSET = TWEAK_WOTS_PK_OFFSET + (V - 1) * TWEAK_LEN

# Buffer size for the hash-chaining trick.
# Each slot is [prefix(4) | hash_output(8)] = 12 elements.
# Poseidon writes its output at offset PP_IN_LEFT (= 4).
# Hash input for the next iteration = slot[0..8] = [prefix(4) | digest(4)].
BUF_SIZE = PP_IN_LEFT + DIGEST_LEN


@inline
def build_left_fn(pp, data, out):
    # out must be Array(DIGEST_LEN) or more.
    for k in unroll(0, PP_IN_LEFT):
        out[k] = pp[k]
    memcopy_4(data, out + PP_IN_LEFT, 0, 1)
    return


@inline
def build_right_fn(tweak, data, out):
    # [tweak(2) | zeros(2) | data(XMSS_DIGEST)]
    # `tweak` points directly to [tw[0], tw[1], 0, 0] in the 4-FE slot.
    memcopy_4(tweak, out, 0, 1)
    memcopy_4(data, out + 4, 0, 1)
    return


@inline
def build_chain_right(public_param, out):
    # Shared chain-hash right input: [public_param(4) | zeros(4)]
    # Built once per xmss_verify and reused for every chain hash.
    for k in unroll(0, PUBLIC_PARAM_LEN_FE):
        out[k] = public_param[k]
    memcopy_4(ZERO_VEC_PTR, out + PUBLIC_PARAM_LEN_FE, 0, 1)
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
    # Right input: [msg[8] | randomness(5) | tweak(2)] = 8 FE
    a_input_right = Array(DIGEST_LEN)
    a_input_right[0] = message[DIGEST_LEN]
    copy_5(randomness, a_input_right + 1)
    a_input_right[1 + RANDOMNESS_LEN] = encoding_tweak[0]
    a_input_right[1 + RANDOMNESS_LEN + 1] = encoding_tweak[1]
    pre_compressed = Array(DIGEST_LEN)
    poseidon16_compress(message, a_input_right, pre_compressed)

    # pp_input layout: [public_param(4) | zeros(4)]
    pp_input = Array(DIGEST_LEN)
    for k in unroll(0, PUBLIC_PARAM_LEN_FE):
        pp_input[k] = public_param[k]
    memcopy_4(ZERO_VEC_PTR, pp_input + PUBLIC_PARAM_LEN_FE, 0, 1)
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

    chain_right = Array(DIGEST_LEN)
    build_chain_right(public_param, chain_right)

    # Single shared buffer for ALL chain hashes: V * CHAIN_LENGTH slots.
    # One memcopy_4 dispatches all chain tweak prefixes at once.
    # Each slot is [prefix(4) | hash_output(8)] = BUF_SIZE.
    # Chain i, step s maps to slot (i * CHAIN_LENGTH + s).
    # Unused slots (steps before starting_step) are harmless.
    ch_shared_bufs = Array(V * CHAIN_LENGTH * BUF_SIZE)
    chain_tweaks_start = tweak_table + TWEAK_CHAIN_OFFSET
    memcopy_4(chain_tweaks_start, ch_shared_bufs, TWEAK_LEN, V * CHAIN_LENGTH)

    for i in unroll(0, V):
        num_hashes = (CHAIN_LENGTH - 1) - encoding[i]
        chain_start = chain_starts + i * XMSS_DIGEST
        chain_end = wots_public_key + i * DIGEST_LEN
        chain_buf_base = ch_shared_bufs + i * CHAIN_LENGTH * BUF_SIZE

        match_range(
            num_hashes,
            range(0, 1),
            lambda _: memcopy_4(chain_start, chain_end, 0, 1),
            range(1, CHAIN_LENGTH),
            lambda n: chain_hash_pa(chain_start, n, chain_end, chain_right, chain_buf_base + (CHAIN_LENGTH - 1 - n) * BUF_SIZE),
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
    # Copy XMSS_DIGEST (= 4) elements from src to dst.
    memcopy_4(src, dst, 0, 1)
    return


@inline
def chain_hash_pa(input, n, output, chain_right, buf_base):
    # Tweak prefixes are already written to all buffer slots by the global memcopy_4.
    # buf_base points to the first slot for this chain (at starting_step within the shared buffer).
    #
    # Each slot is BUF_SIZE = 12: [prefix(4) | hash_output(8)].
    # Poseidon writes its output at slot + PP_IN_LEFT (= 4), so the digest
    # lands at slot[4..8]; together with the prefix at slot[0..4],
    # slot[0..8] forms a valid left input for the NEXT hash.

    # Write input data into first slot
    memcopy_4(input, buf_base + PP_IN_LEFT, 0, 1)

    if n == 1:
        poseidon16_compress(buf_base, chain_right, output)
    else:
        # Poseidon chain: hash slot[j] → slot[j+1] + PP_IN_LEFT
        for j in unroll(0, n - 1):
            cur_buf = buf_base + j * BUF_SIZE
            next_buf = buf_base + (j + 1) * BUF_SIZE
            poseidon16_compress(cur_buf, chain_right, next_buf + PP_IN_LEFT)

        # Final hash: last buf → output
        poseidon16_compress(buf_base + (n - 1) * BUF_SIZE, chain_right, output)
    return


def wots_pk_hash(wots_public_key, public_param, wots_pk_tweaks):
    # Sequential hash over V elements at DIGEST_LEN stride.
    #
    # All V-1 right inputs are allocated contiguously (stride BUF_SIZE=12) so that
    # a single memcopy_4 dispatches all tweak prefixes. Data is then copied individually.
    # Similarly, all V-2 intermediate left buffers get their pp prefix via one broadcast memcopy_4.

    # Right inputs: [tweak(4) | data(4) | unused(4)] = BUF_SIZE each.
    right_bufs = Array((V - 1) * BUF_SIZE)
    memcopy_4(wots_pk_tweaks, right_bufs, TWEAK_LEN, V - 1)
    for i in unroll(0, V - 1):
        memcopy_4(wots_public_key + (i + 1) * DIGEST_LEN, right_bufs + i * BUF_SIZE + 4, 0, 1)

    # First left input: [pp(4) | wots_pk[0](4)]
    left0 = Array(DIGEST_LEN)
    build_left_fn(public_param, wots_public_key, left0)

    # Intermediate left buffers: [pp(4) | digest(4) | poseidon_tail(4)] = BUF_SIZE each.
    left_bufs = Array((V - 2) * BUF_SIZE)
    memcopy_4(public_param, left_bufs, 0, V - 2)

    # Hash chain
    poseidon16_compress(left0, right_bufs, left_bufs + PP_IN_LEFT)

    for i in unroll(1, V - 2):
        poseidon16_compress(
            left_bufs + (i - 1) * BUF_SIZE,
            right_bufs + i * BUF_SIZE,
            left_bufs + i * BUF_SIZE + PP_IN_LEFT,
        )

    # Final hash
    result = Array(DIGEST_LEN)
    poseidon16_compress(left_bufs + (V - 3) * BUF_SIZE, right_bufs + (V - 2) * BUF_SIZE, result)

    return result


@inline
def set_buf_prefix_left(buf, public_param):
    for k in unroll(0, PP_IN_LEFT):
        buf[k] = public_param[k]
    return


@inline
def set_buf_prefix_right(buf, tweak):
    # Write [tw[0], tw[1], 0, 0] to buf[0..4] via memcopy_4.
    memcopy_4(tweak, buf, 0, 1)
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
