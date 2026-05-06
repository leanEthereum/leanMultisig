from snark_lib import *
from utils import *

V = V_PLACEHOLDER
W = W_PLACEHOLDER
CHAIN_LENGTH = 2**W
TARGET_SUM = TARGET_SUM_PLACEHOLDER
LOG_LIFETIME = LOG_LIFETIME_PLACEHOLDER
MESSAGE_LEN = MESSAGE_LEN_PLACEHOLDER
RANDOMNESS_LEN = RANDOMNESS_LEN_PLACEHOLDER
PUBLIC_PARAM_LEN_FE = PUBLIC_PARAM_LEN_FE_PLACEHOLDER
XMSS_DIGEST_LEN = XMSS_DIGEST_LEN_PLACEHOLDER
PUB_KEY_SIZE = XMSS_DIGEST_LEN + PUBLIC_PARAM_LEN_FE
PP_IN_LEFT = DIGEST_LEN - XMSS_DIGEST_LEN
WOTS_SIG_SIZE = RANDOMNESS_LEN + V * XMSS_DIGEST_LEN
# wots_public_key pair stride: each pair occupies 10 cells `[leading_0 | tip_a(4) | tip_b(4) | trailing_0]`. In order to be able to use copy_5 on both sides.
WOTS_PK_PAIR_STRIDE = 2 + 2 * XMSS_DIGEST_LEN
NUM_ENCODING_FE = div_ceil(V, (24 / W))
MERKLE_LEVELS_PER_CHUNK = MERKLE_LEVELS_PER_CHUNK_PLACEHOLDER
N_MERKLE_CHUNKS = LOG_LIFETIME / MERKLE_LEVELS_PER_CHUNK
INNER_PUB_MEM_SIZE = 2**INNER_PUBLIC_MEMORY_LOG_SIZE  # = DIGEST_LEN
TWEAK_TABLE_ADDR = PREAMBLE_MEMORY_END

# Tweak table layout: all tweaks are stored as a 4-FE slot [tw[0], tw[1], 0, 0]
TWEAK_LEN = 4  # stride / slot size for non-encoding tweaks
N_TWEAKS = 1 + V * CHAIN_LENGTH + 1 + LOG_LIFETIME
TWEAK_TABLE_SIZE_FE_PADDED = next_multiple_of(N_TWEAKS * TWEAK_LEN, DIGEST_LEN)
TWEAK_ENCODING_OFFSET = 0
TWEAK_CHAIN_OFFSET = TWEAK_ENCODING_OFFSET + TWEAK_LEN  # just after the encoding tweak
TWEAK_WOTS_PK_OFFSET = TWEAK_CHAIN_OFFSET + V * CHAIN_LENGTH * TWEAK_LEN
TWEAK_MERKLE_OFFSET = TWEAK_WOTS_PK_OFFSET + TWEAK_LEN

@inline
def xmss_verify(pub_key, message, merkle_chunks):
    wots = Array(WOTS_SIG_SIZE)
    hint_witness("wots", wots)

    public_param = pub_key + XMSS_DIGEST_LEN
    randomness = wots
    chain_starts = wots + RANDOMNESS_LEN
   
    # 1) Encode: poseidon16_compress(message[0:8], [randomness(6) | tweak_encoding(2))
    #            poseidon16_compress(pre_compressed, [pp(4) | zeros(4)])
    encoding_tweak = TWEAK_TABLE_ADDR + TWEAK_ENCODING_OFFSET
    a_input_right = Array(DIGEST_LEN)
    copy_6(randomness, a_input_right)
    a_input_right[6] = encoding_tweak[0]
    a_input_right[7] = encoding_tweak[1]
    pre_compressed = Array(DIGEST_LEN)
    poseidon16_compress(message, a_input_right, pre_compressed)
    
    public_params_paded_buff = Array(DIGEST_LEN + 2) # 0 [public_param(4) | zeros(4)] 0
    copy_5(public_param - 1, public_params_paded_buff)
    set_to_5_zeros(public_params_paded_buff + 5)
    public_params_paded = public_params_paded_buff + 1
    encoding_fe = Array(DIGEST_LEN)
    poseidon16_compress(pre_compressed, public_params_paded, encoding_fe)

    # Decompose the encoding into chunks of 2*W bits. Each chunk packs the chain step
    # counts of two consecutive WOTS chains: chunk i = step_{2i} + CHAIN_LENGTH * step_{2i+1}.
    encoding = Array(NUM_ENCODING_FE * 24 / (2 * W))

    hint_decompose_bits_xmss(encoding, encoding_fe, NUM_ENCODING_FE, 2 * W)

    # check that the decomposition is correct
    for i in unroll(0, NUM_ENCODING_FE):
        for j in unroll(0, 24 / (2 * W)):
            assert encoding[i * (24 / (2 * W)) + j] < CHAIN_LENGTH**2

        partial_sum: Mut = encoding[i * (24 / (2 * W))]
        for j in unroll(1, 24 / (2 * W)):
            partial_sum += encoding[i * (24 / (2 * W)) + j] * (CHAIN_LENGTH**2) ** j

        # p = 2^31 - 2^24 + 1 = 127.2^24 + 1, so inv(2^24) = -127 (mod p).
        # Deduce remaining_i from partial_sum + remaining_i * 2^24 == encoding_fe[i]:
        # remaining_i = (encoding_fe[i] - partial_sum) * inv(2^24) = (partial_sum - encoding_fe[i]) * 127
        remaining_i = (partial_sum - encoding_fe[i]) * 127
        assert remaining_i < 127  # ensures uniformity + prevent overflow


    debug_assert(V % 2 == 0)
    wots_public_key = Array((V / 2) * WOTS_PK_PAIR_STRIDE)
    target_sum: Mut = 0
    for i in unroll(0, V / 2):
        chain_start_a = chain_starts + (2 * i) * XMSS_DIGEST_LEN
        chain_start_b = chain_starts + (2 * i + 1) * XMSS_DIGEST_LEN
        chain_end_a = wots_public_key + i * WOTS_PK_PAIR_STRIDE + 1
        chain_end_b = chain_end_a + XMSS_DIGEST_LEN
        tweaks_a = TWEAK_TABLE_ADDR + TWEAK_CHAIN_OFFSET + (2 * i) * CHAIN_LENGTH * TWEAK_LEN
        tweaks_b = TWEAK_TABLE_ADDR + TWEAK_CHAIN_OFFSET + (2 * i + 1) * CHAIN_LENGTH * TWEAK_LEN
        pair_sum_ptr = Array(1)

        match_range(
            encoding[i],
            range(0, CHAIN_LENGTH**2),
            lambda n: chain_hash_pair(
                chain_start_a,
                chain_start_b,
                n,
                chain_end_a,
                chain_end_b,
                tweaks_a,
                tweaks_b,
                public_params_paded,
                pair_sum_ptr,
            ),
        )
        target_sum += pair_sum_ptr[0]

    assert target_sum == TARGET_SUM

    merkle_leaf = wots_pk_hash(wots_public_key, public_param)

    merkle_tweaks = TWEAK_TABLE_ADDR + TWEAK_MERKLE_OFFSET
    xmss_merkle_verify(merkle_leaf, merkle_chunks, pub_key, public_param, merkle_tweaks)
    return


@inline
def chain_hash_pa(input, n, output, chain_i_tweaks, chain_right):
    starting_step = CHAIN_LENGTH - 1 - n
    if n == 1:
        first_tweak = chain_i_tweaks + starting_step * TWEAK_LEN
        poseidon16_compress_half_hardcoded_left(input, chain_right, output, first_tweak)
    else:
        digests = Array(n * XMSS_DIGEST_LEN)

        # Hash 0: input → digests[0..4]
        first_tweak = chain_i_tweaks + starting_step * TWEAK_LEN
        poseidon16_compress_half_hardcoded_left(input, chain_right, digests, first_tweak)

        # Hashes 1..n-2: digests[(j-1)*4..j*4] → digests[j*4..(j+1)*4]
        for j in unroll(1, n - 1):
            cur_tweak = chain_i_tweaks + (starting_step + j) * TWEAK_LEN
            poseidon16_compress_half_hardcoded_left(
                digests + (j - 1) * XMSS_DIGEST_LEN,
                chain_right,
                digests + j * XMSS_DIGEST_LEN,
                cur_tweak,
            )

        # Final hash: digests[(n-2)*4..(n-1)*4] → output
        last_tweak = chain_i_tweaks + (starting_step + n - 1) * TWEAK_LEN
        poseidon16_compress_half_hardcoded_left(
            digests + (n - 2) * XMSS_DIGEST_LEN, chain_right, output, last_tweak
        )
    return


@inline
def chain_hash_pair(
    input_a,
    input_b,
    n,
    output_a,
    output_b,
    tweaks_a,
    tweaks_b,
    chain_right,
    pair_sum_ptr,
):
    # Pair-encoded chain hash. `n` is a compile-time constant in [0, CHAIN_LENGTH^2)
    raw_a = n % CHAIN_LENGTH
    raw_b = (n - raw_a) / CHAIN_LENGTH
    num_hashes_a = (CHAIN_LENGTH - 1) - raw_a
    num_hashes_b = (CHAIN_LENGTH - 1) - raw_b

    if num_hashes_a == 0:
        copy_5(input_a - 1, output_a - 1)
    else:
        chain_hash_pa(input_a, num_hashes_a, output_a, tweaks_a, chain_right)

    if num_hashes_b == 0:
        copy_5(input_b, output_b)
    else:
        chain_hash_pa(input_b, num_hashes_b, output_b, tweaks_b, chain_right)

    pair_sum_ptr[0] = raw_a + raw_b
    return


@inline
def wots_pk_hash(wots_public_key, public_param):
    N_CHUNKS = V / 2
    states = Array((N_CHUNKS + 1) * DIGEST_LEN)
    poseidon16_compress_hardcoded_left(
        public_param, ZERO_VEC_PTR, states, TWEAK_TABLE_ADDR + TWEAK_WOTS_PK_OFFSET
    )
    for i in unroll(0, N_CHUNKS):
        poseidon16_compress(
            states + i * DIGEST_LEN,
            wots_public_key + i * WOTS_PK_PAIR_STRIDE + 1,
            states + (i + 1) * DIGEST_LEN,
        )

    return states + N_CHUNKS * DIGEST_LEN


@inline
def set_buf_prefix_right(buf, public_param):
    # Writes [pp(4)] to buf[0..4] — the RIGHT-input prefix.
    for k in unroll(0, PP_IN_LEFT):
        buf[k] = public_param[k]
    return


@inline
def do_4_merkle_levels(b, state_in, state_out, public_param, merkle_tweaks_chunk):
    b0 = b % 2
    r1 = (b - b0) / 2
    b1 = r1 % 2
    r2 = (r1 - b1) / 2
    b2 = r2 % 2
    r3 = (r2 - b2) / 2
    b3 = r3 % 2

    buf0_alloc = Array(XMSS_DIGEST_LEN * 2 + 2)
    buf0 = buf0_alloc + 1
    if b0 == 1:
        # state_in is the LEFT child → state_in[0..4] lands at buf0[0..4].
        copy_5(state_in - 1, buf0 - 1)
        hint_witness("xmss_merkle_node", buf0 + XMSS_DIGEST_LEN)
    else:
        # state_in is the RIGHT child → state_in[0..4] lands at buf0[4..8].
        hint_witness("xmss_merkle_node", buf0)
        copy_5(state_in, buf0 + XMSS_DIGEST_LEN)

    # Level 0 hash
    buf1 = Array(XMSS_DIGEST_LEN * 2)
    if b1 == 1:
        poseidon16_compress_half_hardcoded_left(public_param, buf0, buf1, merkle_tweaks_chunk)
        hint_witness("xmss_merkle_node", buf1 + XMSS_DIGEST_LEN)
    else:
        poseidon16_compress_half_hardcoded_left(public_param, buf0, buf1 + XMSS_DIGEST_LEN, merkle_tweaks_chunk)
        hint_witness("xmss_merkle_node", buf1)

    # Level 1 hash → buf2
    buf2 = Array(XMSS_DIGEST_LEN * 2)
    if b2 == 1:
        poseidon16_compress_half_hardcoded_left(public_param, buf1, buf2, merkle_tweaks_chunk + 1 * TWEAK_LEN)
        hint_witness("xmss_merkle_node", buf2 + XMSS_DIGEST_LEN)
    else:
        poseidon16_compress_half_hardcoded_left(public_param, buf1, buf2 + XMSS_DIGEST_LEN, merkle_tweaks_chunk + 1 * TWEAK_LEN)
        hint_witness("xmss_merkle_node", buf2)

    # Level 2 hash → buf3
    buf3 = Array(XMSS_DIGEST_LEN * 2)
    if b3 == 1:
        poseidon16_compress_half_hardcoded_left(public_param, buf2, buf3, merkle_tweaks_chunk + 2 * TWEAK_LEN)
        hint_witness("xmss_merkle_node", buf3 + XMSS_DIGEST_LEN)
    else:
        poseidon16_compress_half_hardcoded_left(public_param, buf2, buf3 + XMSS_DIGEST_LEN, merkle_tweaks_chunk + 2 * TWEAK_LEN)
        hint_witness("xmss_merkle_node", buf3)

    poseidon16_compress_half_hardcoded_left(public_param, buf3, state_out, merkle_tweaks_chunk + 3 * TWEAK_LEN)
    return


@inline
def xmss_merkle_verify(leaf_digest, merkle_chunks, expected_root, public_param, merkle_tweaks):
    states_alloc = Array(DIM * N_MERKLE_CHUNKS)
    states = states_alloc + 1

    # First chunk
    match_range(merkle_chunks[0], range(0, 16), lambda b: do_4_merkle_levels(b, leaf_digest, states, public_param, merkle_tweaks))

    state_indexes = Array(N_MERKLE_CHUNKS - 1)
    state_indexes[0] = states
    for j in unroll(1, N_MERKLE_CHUNKS - 1):
        state_indexes[j] = state_indexes[j - 1] + DIM
        match_range(
            merkle_chunks[j],
            range(0, 16),
            lambda b: do_4_merkle_levels(
                b,
                state_indexes[j - 1],
                state_indexes[j],
                public_param,
                merkle_tweaks + j * MERKLE_LEVELS_PER_CHUNK * TWEAK_LEN,
            ),
        )

    # last chunk → write directly to expected_root
    match_range(
        merkle_chunks[N_MERKLE_CHUNKS - 1],
        range(0, 16),
        lambda b: do_4_merkle_levels(
            b,
            state_indexes[N_MERKLE_CHUNKS - 2],
            expected_root,
            public_param,
            merkle_tweaks + (N_MERKLE_CHUNKS - 1) * MERKLE_LEVELS_PER_CHUNK * TWEAK_LEN,
        ),
    )
    return
