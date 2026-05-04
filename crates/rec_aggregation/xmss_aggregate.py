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
PP_IN_LEFT = DIGEST_LEN - XMSS_DIGEST_LEN  # = 2 (Goldilocks: pp(2)|zeros(2))
WOTS_SIG_SIZE = RANDOMNESS_LEN + V * XMSS_DIGEST_LEN
# wots_public_key pair stride: each pair occupies (1 + 2*XMSS_DIGEST_LEN + 1) cells.
# `[leading_0 | tip_a(2) | tip_b(2) | trailing_0]` so that copy_ef can be used on
# both halves under Goldilocks (DIM = 3 = 1 + XMSS_DIGEST_LEN).
WOTS_PK_PAIR_STRIDE = 2 + 2 * XMSS_DIGEST_LEN
NUM_ENCODING_FE = 4
LOW_BITS_PER_ENCODING_FE = 32
MERKLE_LEVELS_PER_CHUNK = MERKLE_LEVELS_PER_CHUNK_PLACEHOLDER
N_MERKLE_CHUNKS = LOG_LIFETIME / MERKLE_LEVELS_PER_CHUNK
INNER_PUB_MEM_SIZE = 2**INNER_PUBLIC_MEMORY_LOG_SIZE  # = DIGEST_LEN
TWEAK_TABLE_ADDR = PREAMBLE_MEMORY_END

# Tweak table layout: each tweak is stored in a 2-FE slot [tw[0], 0]. Goldilocks
# tweaks are 1 FE + 1 zero pad so the slot stride is 2 (= XMSS_DIGEST_LEN).
TWEAK_LEN = 2  # stride / slot size for tweaks (1 actual + 1 zero)
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

    # 1) Encode: poseidon8_compress(message[0:4], [randomness(3) | tweak_encoding(1)])
    #            poseidon8_compress(pre_compressed, [pp(2) | zeros(2)])
    encoding_tweak = TWEAK_TABLE_ADDR + TWEAK_ENCODING_OFFSET
    a_input_right = Array(DIGEST_LEN)
    copy_ef(randomness, a_input_right)
    a_input_right[3] = encoding_tweak[0]
    pre_compressed = Array(DIGEST_LEN)
    poseidon8_compress(message, a_input_right, pre_compressed)

    # `[0 | pp(2) | zeros(2) | 0]` so poseidon8_compress_hardcoded_left could be applied later
    # (here we just need the right operand layout `[pp(2) | zeros(2)]`).
    public_params_paded_buff = Array(DIGEST_LEN + 2)
    copy_ef(public_param - 1, public_params_paded_buff)
    zero_ef(public_params_paded_buff + 3)
    public_params_paded = public_params_paded_buff + 1
    encoding_fe = Array(DIGEST_LEN)
    poseidon8_compress(pre_compressed, public_params_paded, encoding_fe)

    encoding = Array(V)
    for i in unroll(0, NUM_ENCODING_FE):
        decompose_encoding_fe(encoding_fe[i], encoding + i * (V / NUM_ENCODING_FE))

    debug_assert(V % 2 == 0)
    wots_public_key = Array((V / 2) * WOTS_PK_PAIR_STRIDE)
    target_sum: Mut = 0
    # Pair structure: `[leading_0 | tip_a(XMSS_DIGEST_LEN) | tip_b(XMSS_DIGEST_LEN) | trailing_0]`
    # so a length-DIM block straddles each tip with one zero-pad cell.
    for i in unroll(0, V / 2):
        chain_start_a = chain_starts + (2 * i) * XMSS_DIGEST_LEN
        chain_start_b = chain_starts + (2 * i + 1) * XMSS_DIGEST_LEN
        chain_end_a = wots_public_key + i * WOTS_PK_PAIR_STRIDE + 1
        chain_end_b = chain_end_a + XMSS_DIGEST_LEN
        tweaks_a = TWEAK_TABLE_ADDR + TWEAK_CHAIN_OFFSET + (2 * i) * CHAIN_LENGTH * TWEAK_LEN
        tweaks_b = TWEAK_TABLE_ADDR + TWEAK_CHAIN_OFFSET + (2 * i + 1) * CHAIN_LENGTH * TWEAK_LEN
        len_a_ptr = Array(1)
        len_b_ptr = Array(1)

        match_range(
            encoding[2 * i],
            range(0, CHAIN_LENGTH),
            lambda n: chain_hash_a(
                chain_start_a, n, chain_end_a, tweaks_a, public_params_paded, len_a_ptr,
            ),
        )
        match_range(
            encoding[2 * i + 1],
            range(0, CHAIN_LENGTH),
            lambda n: chain_hash_b(
                chain_start_b, n, chain_end_b, tweaks_b, public_params_paded, len_b_ptr,
            ),
        )
        target_sum += len_a_ptr[0]
        target_sum += len_b_ptr[0]

    assert target_sum == TARGET_SUM

    merkle_leaf = wots_pk_hash(wots_public_key, public_param)

    merkle_tweaks = TWEAK_TABLE_ADDR + TWEAK_MERKLE_OFFSET
    xmss_merkle_verify(merkle_leaf, merkle_chunks, pub_key, public_param, merkle_tweaks)
    return


@inline
def chain_hash_inner(input, n, output, chain_i_tweaks, chain_right):
    # Iterate the WOTS chain hash `num_hashes = (CHAIN_LENGTH-1) - n` times,
    # starting from `input`, writing the final chain tip to `output`.
    # Caller is responsible for the n=0 case (a copy from input).
    num_hashes = (CHAIN_LENGTH - 1) - n
    starting_step = CHAIN_LENGTH - 1 - num_hashes

    if num_hashes == 1:
        first_tweak = chain_i_tweaks + starting_step * TWEAK_LEN
        poseidon8_compress_half_hardcoded_left(input, chain_right, output, first_tweak)
    else:
        digests = Array(num_hashes * XMSS_DIGEST_LEN)

        # Hash 0: input → digests[0..XMSS_DIGEST_LEN]
        first_tweak = chain_i_tweaks + starting_step * TWEAK_LEN
        poseidon8_compress_half_hardcoded_left(input, chain_right, digests, first_tweak)

        # Hashes 1..num_hashes-2
        for j in unroll(1, num_hashes - 1):
            cur_tweak = chain_i_tweaks + (starting_step + j) * TWEAK_LEN
            poseidon8_compress_half_hardcoded_left(
                digests + (j - 1) * XMSS_DIGEST_LEN,
                chain_right,
                digests + j * XMSS_DIGEST_LEN,
                cur_tweak,
            )

        # Final hash → output
        last_tweak = chain_i_tweaks + (starting_step + num_hashes - 1) * TWEAK_LEN
        poseidon8_compress_half_hardcoded_left(
            digests + (num_hashes - 2) * XMSS_DIGEST_LEN, chain_right, output, last_tweak
        )
    return


@inline
def chain_hash_a(input, n, output, chain_i_tweaks, chain_right, chain_length_ptr):
    # Even (chain_a) variant: when num_hashes == 0, the buffer slot occupies
    # `[output-1 .. output+XMSS_DIGEST_LEN)` (= leading_0 | tip_a) so copy_ef
    # writes through the leading zero cell.
    debug_assert(n < CHAIN_LENGTH)
    num_hashes = (CHAIN_LENGTH - 1) - n
    if num_hashes == 0:
        copy_ef(input - 1, output - 1)
    else:
        chain_hash_inner(input, n, output, chain_i_tweaks, chain_right)
    chain_length_ptr[0] = n
    return


@inline
def chain_hash_b(input, n, output, chain_i_tweaks, chain_right, chain_length_ptr):
    # Odd (chain_b) variant: when num_hashes == 0, the buffer slot occupies
    # `[output .. output+XMSS_DIGEST_LEN+1)` (= tip_b | trailing_0) so copy_ef
    # writes through the trailing zero cell.
    debug_assert(n < CHAIN_LENGTH)
    num_hashes = (CHAIN_LENGTH - 1) - n
    if num_hashes == 0:
        copy_ef(input, output)
    else:
        chain_hash_inner(input, n, output, chain_i_tweaks, chain_right)
    chain_length_ptr[0] = n
    return


@inline
def decompose_encoding_fe(fe_value, chunks_ptr):
    limbs = Array(2)
    hint_decompose_bits_xmss(chunks_ptr, limbs, fe_value)

    for k in unroll(0, 10):
        assert chunks_ptr[k] < CHAIN_LENGTH
    assert limbs[0] < 2**16
    assert limbs[1] < 2**16

    low: Mut = chunks_ptr[0]
    for k in unroll(1, 10):
        low += chunks_ptr[k] * (2 ** (W * k))

    high = limbs[0] + limbs[1] * (2**16)
    assert fe_value == low + (2**32) * high
    assert high != 2**32 - 1 # ensures uniformity + prevents overflow

    return


@inline
def wots_pk_hash(wots_public_key, public_param):
    # T-Sponge with replacement: IV = poseidon8([tweak(1)|0|pp(2)], zeros)
    # then absorb pairs of WOTS chain tips.
    N_CHUNKS = V / 2
    states = Array((N_CHUNKS + 1) * DIGEST_LEN)
    poseidon8_compress_hardcoded_left(
        public_param, ZERO_VEC_PTR, states, TWEAK_TABLE_ADDR + TWEAK_WOTS_PK_OFFSET
    )
    for i in unroll(0, N_CHUNKS):
        poseidon8_compress(
            states + i * DIGEST_LEN,
            wots_public_key + i * WOTS_PK_PAIR_STRIDE + 1,
            states + (i + 1) * DIGEST_LEN,
        )

    return states + N_CHUNKS * DIGEST_LEN


@inline
def do_4_merkle_levels(b, state_in, state_out, public_param, merkle_tweaks_chunk):
    b0 = b % 2
    r1 = (b - b0) / 2
    b1 = r1 % 2
    r2 = (r1 - b1) / 2
    b2 = r2 % 2
    r3 = (r2 - b2) / 2
    b3 = r3 % 2

    # buf0 layout: [0 | left_child(2) | right_child(2) | 0] (stride DIM=3 on each side)
    buf0_alloc = Array(XMSS_DIGEST_LEN * 2 + 2)
    buf0 = buf0_alloc + 1
    if b0 == 1:
        # state_in is the LEFT child → buf0[0..XMSS_DIGEST_LEN].
        copy_ef(state_in - 1, buf0 - 1)
        hint_witness("xmss_merkle_node", buf0 + XMSS_DIGEST_LEN)
    else:
        # state_in is the RIGHT child → buf0[XMSS_DIGEST_LEN..2*XMSS_DIGEST_LEN].
        hint_witness("xmss_merkle_node", buf0)
        copy_ef(state_in, buf0 + XMSS_DIGEST_LEN)

    # Level 0 hash → buf1
    buf1 = Array(XMSS_DIGEST_LEN * 2)
    if b1 == 1:
        poseidon8_compress_half_hardcoded_left(public_param, buf0, buf1, merkle_tweaks_chunk)
        hint_witness("xmss_merkle_node", buf1 + XMSS_DIGEST_LEN)
    else:
        poseidon8_compress_half_hardcoded_left(public_param, buf0, buf1 + XMSS_DIGEST_LEN, merkle_tweaks_chunk)
        hint_witness("xmss_merkle_node", buf1)

    # Level 1 hash → buf2
    buf2 = Array(XMSS_DIGEST_LEN * 2)
    if b2 == 1:
        poseidon8_compress_half_hardcoded_left(public_param, buf1, buf2, merkle_tweaks_chunk + 1 * TWEAK_LEN)
        hint_witness("xmss_merkle_node", buf2 + XMSS_DIGEST_LEN)
    else:
        poseidon8_compress_half_hardcoded_left(public_param, buf1, buf2 + XMSS_DIGEST_LEN, merkle_tweaks_chunk + 1 * TWEAK_LEN)
        hint_witness("xmss_merkle_node", buf2)

    # Level 2 hash → buf3
    buf3 = Array(XMSS_DIGEST_LEN * 2)
    if b3 == 1:
        poseidon8_compress_half_hardcoded_left(public_param, buf2, buf3, merkle_tweaks_chunk + 2 * TWEAK_LEN)
        hint_witness("xmss_merkle_node", buf3 + XMSS_DIGEST_LEN)
    else:
        poseidon8_compress_half_hardcoded_left(public_param, buf2, buf3 + XMSS_DIGEST_LEN, merkle_tweaks_chunk + 2 * TWEAK_LEN)
        hint_witness("xmss_merkle_node", buf3)

    poseidon8_compress_half_hardcoded_left(public_param, buf3, state_out, merkle_tweaks_chunk + 3 * TWEAK_LEN)
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
