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

# Tweak table layout: each tweak is stored as a 5-FE padded slot [0, tw[0], tw[1], 0, 0].
# Convention: tweak pointers always point to the tweak VALUE (offset +1 within the slot).
# Individual access: ptr[0] = tw[0], ptr[1] = tw[1] (unchanged from the unpadded version).
# Copy_5 access: copy_5(ptr - 1, dst) reads the 5-element slot [0, tw[0], tw[1], 0, 0].
TWEAK_LEN = 5  # stride / slot size in the padded table
N_TWEAKS = 1 + V * CHAIN_LENGTH + (V - 1) + LOG_LIFETIME
TWEAK_TABLE_SIZE_FE_PADDED = next_multiple_of(N_TWEAKS * TWEAK_LEN, DIGEST_LEN)
TWEAK_ENCODING_OFFSET = 1  # skip the leading zero of slot 0
TWEAK_CHAIN_OFFSET = TWEAK_ENCODING_OFFSET + TWEAK_LEN
TWEAK_WOTS_PK_OFFSET = TWEAK_CHAIN_OFFSET + V * CHAIN_LENGTH * TWEAK_LEN
TWEAK_MERKLE_OFFSET = TWEAK_WOTS_PK_OFFSET + (V - 1) * TWEAK_LEN

# Buffer size for the hash-chaining trick.
# Each slot is [extra(1) | prefix(4) | hash_output(8)] = 13 elements.
# The "extra" position at offset 0 is the landing spot for copy_5's leading zero when
# writing a padded tweak from the table. The effective buffer (hash-input pointer) is at
# offset 1; poseidon writes its output at offset 5 (= 1 + PP_IN_LEFT).
# Hash input for the next iteration = slot[1..9] = [prefix(4) | digest(4)].
BUF_SIZE = 1 + PP_IN_LEFT + DIGEST_LEN


@inline
def build_left_fn(tweak, data, out):
    # [tweak(2) | zeros(2) | data(XMSS_DIGEST)]
    # `tweak` is a pointer to the tweak VALUE (slot_start + 1). copy_5(tweak - 1, out - 1)
    # writes the padded slot [0, tw(2), 0, 0] to out[-1..4]; the leading 0 lands at the
    # "extra" slot before `out`.
    # `out` must be allocated as `alloc + 1` where alloc is Array(DIGEST_LEN + 2) or more
    # (so that out[-1] and out[0..9] are all valid writable memory).
    copy_5(tweak - 1, out - 1)
    copy_5(data, out + 4)
    return


@inline
def build_right_fn(pp, data, out):
    # [public_param(4) | data(XMSS_DIGEST)]
    # out must be Array(DIGEST_LEN + 1) or more.
    # data must have at least 5 readable elements in memory.
    for k in unroll(0, PP_IN_LEFT):
        out[k] = pp[k]
    copy_5(data, out + PP_IN_LEFT)
    return


@inline
def build_chain_right(public_param, out):
    # Shared chain-hash right input: [public_param(4) | zeros(4)]
    # Built once per xmss_verify and reused for every chain hash.
    # out must be Array(DIGEST_LEN + 1) so set_to_5_zeros can write positions 4..8.
    for k in unroll(0, PUBLIC_PARAM_LEN_FE):
        out[k] = public_param[k]
    set_to_5_zeros(out + PUBLIC_PARAM_LEN_FE)
    return


@inline
def set_chain_left_prefix(cur_buf, tweak):
    # Writes [tweak(2) | zeros(2)] to cur_buf[0..4].
    cur_buf[0] = tweak[0]
    cur_buf[1] = tweak[1]
    cur_buf[2] = 0
    cur_buf[3] = 0
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
    # Allocate 11 elements so the 2nd copy_5 (which reads [tw(2), 0, 0, 0] from the padded
    # table and writes 5 elements at offset 6) can safely write positions 6..11.
    a_input_right = Array(1 + RANDOMNESS_LEN + TWEAK_LEN)
    a_input_right[0] = message[DIGEST_LEN]
    copy_5(randomness, a_input_right + 1)
    # encoding_tweak points to the tweak VALUE; reading 5 elements gives [tw(2), 0, 0, 0].
    copy_5(encoding_tweak, a_input_right + 1 + RANDOMNESS_LEN)
    pre_compressed = Array(DIGEST_LEN)
    poseidon16_compress(message, a_input_right, pre_compressed)

    # pp_input layout: [public_param(4) | zeros(4)]. Allocate 9 so set_to_5_zeros can write positions 4..8.
    pp_input = Array(DIGEST_LEN + 1)
    for k in unroll(0, PUBLIC_PARAM_LEN_FE):
        pp_input[k] = public_param[k]
    set_to_5_zeros(pp_input + PUBLIC_PARAM_LEN_FE)
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

    chain_right = Array(DIGEST_LEN + 1)
    build_chain_right(public_param, chain_right)

    for i in unroll(0, V):
        num_hashes = (CHAIN_LENGTH - 1) - encoding[i]
        chain_start = chain_starts + i * XMSS_DIGEST
        chain_end = wots_public_key + i * DIGEST_LEN
        chain_i_tweaks = tweak_table + TWEAK_CHAIN_OFFSET + i * CHAIN_LENGTH * TWEAK_LEN

        # Pre-allocate all buffers (constant allocation regardless of num_hashes).
        # Each slot starts with an "extra" element at offset 0, used as the landing spot
        # for copy_5's leading zero when writing the padded tweak prefix.
        # We allocate 1 extra element BEFORE the first slot and expose pointers pointing
        # at slot_start + 1 (the hash-input position). Thus `ptr - 1` is always valid.
        ch_left_first_alloc = Array(BUF_SIZE)
        ch_left_first = ch_left_first_alloc + 1
        ch_bufs_alloc = Array((MAX_CHAIN_HASHES - 1) * BUF_SIZE)
        ch_bufs = ch_bufs_alloc + 1
        ch_buf_idx = Array(MAX_CHAIN_HASHES - 1)

        match_range(
            num_hashes,
            range(0, 1),
            lambda _: copy_5(chain_start, chain_end),
            range(1, CHAIN_LENGTH),
            lambda n: chain_hash_pa(chain_start, n, chain_end, chain_i_tweaks, chain_right, ch_left_first, ch_bufs, ch_buf_idx),
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
def chain_hash_pa(input, n, output, chain_i_tweaks, chain_right, ch_left_first, ch_bufs, ch_buf_idx):
    # Uses pre-allocated buffers (zero internal allocation for parallel_range compatibility).
    # Chain hash layout: left = [tweak(2) | zeros(2) | data(4)], right = chain_right (shared).
    #
    # Each slot is BUF_SIZE = 13: [extra(1) | prefix(4) | hash_output(8)].
    # The "hash-input" pointer for a slot is slot_start + 1 (skipping the extra).
    # copy_5 writes to slot_start (5 elements, leading zero lands in extra slot).
    # Poseidon writes its output at slot_start + 5 (= hash_input_ptr + 4), so the digest
    # lands at hash_input_ptr[4..8]; together with the prefix at hash_input_ptr[0..4],
    # the slot's hash_input_ptr[0..8] forms a valid left input for the NEXT hash.
    #
    # ch_left_first, ch_bufs, ch_buf_idx all store HASH-INPUT pointers (= slot_start + 1).
    # copy_5 destination = ptr - 1 (the slot start).
    starting_step = CHAIN_LENGTH - 1 - n

    # Build L_0 = [tweak_0, zeros, input]
    # first_tweak is a pointer to the tweak VALUE (slot_start + 1); copy_5 reads from
    # first_tweak - 1 (the slot_start including its leading zero).
    first_tweak = chain_i_tweaks + starting_step * TWEAK_LEN
    copy_5(first_tweak - 1, ch_left_first - 1)  # writes ch_left_first[-1..4]
    copy_5(input, ch_left_first + 4)  # writes ch_left_first[4..9] = input(4) + extra

    if n == 1:
        poseidon16_compress(ch_left_first, chain_right, output)
    else:
        # Hash 0: L_0 → ch_bufs[0] + 4 (writes bufs[0][4..12], digest at bufs[0][4..8])
        ch_buf_idx[0] = ch_bufs
        poseidon16_compress(ch_left_first, chain_right, ch_bufs + 4)
        # Write L_1 prefix via copy_5 of padded tweak_1 to ch_bufs - 1 (the extra slot).
        next_tweak = chain_i_tweaks + (starting_step + 1) * TWEAK_LEN
        copy_5(next_tweak - 1, ch_bufs - 1)

        # Hashes 1..n-2: buf[j-1] → buf[j] + 4
        for j in unroll(1, n - 1):
            ch_buf_idx[j] = ch_buf_idx[j - 1] + BUF_SIZE
            cur_buf = ch_buf_idx[j]
            poseidon16_compress(ch_buf_idx[j - 1], chain_right, cur_buf + 4)
            cur_tweak = chain_i_tweaks + (starting_step + j + 1) * TWEAK_LEN
            copy_5(cur_tweak - 1, cur_buf - 1)

        # Final hash: buf[n-2] → output
        poseidon16_compress(ch_buf_idx[n - 2], chain_right, output)
    return


def wots_pk_hash(wots_public_key, public_param, wots_pk_tweaks):
    # Sponge-like hash of V public key digests.
    # IV = [tweak(2) | pp(4) | 00(2)], then ingest 8 FE per step (2 digests).
    # V must be even. Digests in wots_public_key are at stride DIGEST_LEN (=8).
    N_CHUNKS = V / 2

    # Build IV: [tweak(2) | 0 | pp(4) | 0]
    iv = Array(DIGEST_LEN)
    iv[0] = wots_pk_tweaks[0]
    iv[1] = wots_pk_tweaks[1]
    iv[2] = 0
    for k in unroll(0, PUBLIC_PARAM_LEN_FE):
        iv[3 + k] = public_param[k]
    iv[7] = 0

    # Ingest V digests, 2 at a time (8 FE per chunk)
    # Each chunk packs pk[2i] and pk[2i+1] (each XMSS_DIGEST FE, at DIGEST_LEN stride)
    chunks = Array(N_CHUNKS * DIGEST_LEN)
    for i in unroll(0, N_CHUNKS):
        for k in unroll(0, XMSS_DIGEST):
            chunks[i * DIGEST_LEN + k] = wots_public_key[(2 * i) * DIGEST_LEN + k]
            chunks[i * DIGEST_LEN + XMSS_DIGEST + k] = wots_public_key[(2 * i + 1) * DIGEST_LEN + k]

    states = Array(N_CHUNKS * DIGEST_LEN)
    poseidon16_compress(iv, chunks, states)
    for i in unroll(1, N_CHUNKS):
        poseidon16_compress(states + (i - 1) * DIGEST_LEN, chunks + i * DIGEST_LEN, states + i * DIGEST_LEN)

    return states + (N_CHUNKS - 1) * DIGEST_LEN


@inline
def set_buf_prefix_left(buf, tweak):
    # Writes [tweak(2) | zeros(2)] to buf[0..4] — the LEFT-input prefix.
    # `tweak` points to the tweak VALUE (slot_start + 1). copy_5 reads the padded slot
    # [0, tw[0], tw[1], 0, 0] and writes buf[-1..4]; the leading 0 lands at the "extra"
    # slot before buf, and buf[0..4] = [tw[0], tw[1], 0, 0] — the desired prefix.
    # buf must be `alloc + 1` where alloc has at least BUF_SIZE + 1 elements.
    copy_5(tweak - 1, buf - 1)
    return


@inline
def set_buf_prefix_right(buf, public_param):
    # Writes [pp(4)] to buf[0..4] — the RIGHT-input prefix.
    for k in unroll(0, PP_IN_LEFT):
        buf[k] = public_param[k]
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
    # All `Array(DIGEST_LEN + 2)` allocations reserve 1 element at offset 0 as the "extra"
    # landing spot for build_left_fn's copy_5 prefix trick; the effective pointer is alloc+1.
    left0_alloc = Array(DIGEST_LEN + 2)
    left0 = left0_alloc + 1
    right0_alloc = Array(DIGEST_LEN + 2)
    right0 = right0_alloc + 1
    if b0 == 1:
        build_left_fn(merkle_tweaks_chunk, state_in, left0)
        build_right_fn(public_param, path_chunk, right0)
    else:
        build_left_fn(merkle_tweaks_chunk, path_chunk, left0)
        build_right_fn(public_param, state_in, right0)

    # Buffer trick: hash output to buf + PP_IN_LEFT, then prepend prefix.
    # buf*_alloc has a leading "extra" slot so set_buf_prefix_left can use copy_5.
    buf0_alloc = Array(BUF_SIZE + 1)
    buf0 = buf0_alloc + 1
    poseidon16_compress(left0, right0, buf0 + PP_IN_LEFT)

    # Level 1
    other1_alloc = Array(DIGEST_LEN + 2)
    other1 = other1_alloc + 1
    buf1_alloc = Array(BUF_SIZE + 1)
    buf1 = buf1_alloc + 1
    if b1 == 1:
        set_buf_prefix_left(buf0, merkle_tweaks_chunk + 1 * TWEAK_LEN)
        build_right_fn(public_param, path_chunk + 1 * XMSS_DIGEST, other1)
        poseidon16_compress(buf0, other1, buf1 + PP_IN_LEFT)
    else:
        set_buf_prefix_right(buf0, public_param)
        build_left_fn(merkle_tweaks_chunk + 1 * TWEAK_LEN, path_chunk + 1 * XMSS_DIGEST, other1)
        poseidon16_compress(other1, buf0, buf1 + PP_IN_LEFT)

    # Level 2
    other2_alloc = Array(DIGEST_LEN + 2)
    other2 = other2_alloc + 1
    buf2_alloc = Array(BUF_SIZE + 1)
    buf2 = buf2_alloc + 1
    if b2 == 1:
        set_buf_prefix_left(buf1, merkle_tweaks_chunk + 2 * TWEAK_LEN)
        build_right_fn(public_param, path_chunk + 2 * XMSS_DIGEST, other2)
        poseidon16_compress(buf1, other2, buf2 + PP_IN_LEFT)
    else:
        set_buf_prefix_right(buf1, public_param)
        build_left_fn(merkle_tweaks_chunk + 2 * TWEAK_LEN, path_chunk + 2 * XMSS_DIGEST, other2)
        poseidon16_compress(other2, buf1, buf2 + PP_IN_LEFT)

    # Level 3 -> state_out
    other3_alloc = Array(DIGEST_LEN + 2)
    other3 = other3_alloc + 1
    if b3 == 1:
        set_buf_prefix_left(buf2, merkle_tweaks_chunk + 3 * TWEAK_LEN)
        build_right_fn(public_param, path_chunk + 3 * XMSS_DIGEST, other3)
        poseidon16_compress(buf2, other3, state_out)
    else:
        set_buf_prefix_right(buf2, public_param)
        build_left_fn(merkle_tweaks_chunk + 3 * TWEAK_LEN, path_chunk + 3 * XMSS_DIGEST, other3)
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
