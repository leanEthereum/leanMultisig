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
PRIVATE_INPUT_START = PREAMBLE_MEMORY_END
TWEAK_TABLE_ADDR = PRIVATE_INPUT_START

# Tweak table layout: all tweaks are stored as a 4-FE slot [tw[0], tw[1], 0, 0], except the first, encoding, tweak: which is 5-FE [tw[0], tw[1], 0, 0, 0] (in order to use copy_5)
TWEAK_LEN = 4  # stride / slot size for non-encoding tweaks
ENCODING_TWEAK_SLOT_SIZE = 5  # encoding tweak has one extra trailing zero
N_TWEAKS = 1 + V * CHAIN_LENGTH + 1 + LOG_LIFETIME
TWEAK_TABLE_SIZE_FE_PADDED = next_multiple_of(ENCODING_TWEAK_SLOT_SIZE + (N_TWEAKS - 1) * TWEAK_LEN, DIGEST_LEN)
TWEAK_ENCODING_OFFSET = 0
TWEAK_CHAIN_OFFSET = ENCODING_TWEAK_SLOT_SIZE  # encoding occupies cells [0..5]
TWEAK_WOTS_PK_OFFSET = TWEAK_CHAIN_OFFSET + V * CHAIN_LENGTH * TWEAK_LEN
TWEAK_MERKLE_OFFSET = TWEAK_WOTS_PK_OFFSET + TWEAK_LEN

@inline
def xmss_verify(pub_key, message, merkle_chunks):
    wots = Array(WOTS_SIG_SIZE)
    hint_wots(wots)

    public_param = pub_key + XMSS_DIGEST_LEN
    randomness = wots
    chain_starts = wots + RANDOMNESS_LEN
   
    # 1) Encode: poseidon16_compress(message[0:8], [randomness(5) | tweak_encoding(2) | 0])
    #            poseidon16_compress(pre_compressed, [pp(4) | zeros(4)])
    encoding_tweak = TWEAK_TABLE_ADDR + TWEAK_ENCODING_OFFSET
    a_input_right = Array(RANDOMNESS_LEN + ENCODING_TWEAK_SLOT_SIZE)
    copy_5(randomness, a_input_right)
    # encoding_tweak points to tw[0] of slot 0; reading 5 elements gives [tw(2), 0, 0, 0].
    copy_5(encoding_tweak, a_input_right + RANDOMNESS_LEN)
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
    remaining = Array(NUM_ENCODING_FE)

    hint_decompose_bits_xmss(encoding, remaining, encoding_fe, NUM_ENCODING_FE, 2 * W)

    # check that the decomposition is correct
    for i in unroll(0, NUM_ENCODING_FE):
        for j in unroll(0, 24 / (2 * W)):
            assert encoding[i * (24 / (2 * W)) + j] < CHAIN_LENGTH**2

        assert remaining[i] < 2**7 - 1

        partial_sum: Mut = remaining[i] * 2**24
        for j in unroll(0, 24 / (2 * W)):
            partial_sum += encoding[i * (24 / (2 * W)) + j] * (CHAIN_LENGTH**2) ** j
        assert partial_sum == encoding_fe[i]


    debug_assert(V % 2 == 0)
    wots_public_key = Array((V / 2) * WOTS_PK_PAIR_STRIDE)
    target_sum: Mut = 0
    for i in unroll(0, V / 2):
        chain_start_a = chain_starts + (2 * i) * XMSS_DIGEST_LEN
        chain_start_b = chain_starts + (2 * i + 1) * XMSS_DIGEST_LEN
        chain_end_a = wots_public_key + i * WOTS_PK_PAIR_STRIDE + 1
        chain_end_b = wots_public_key + i * WOTS_PK_PAIR_STRIDE + 1 + XMSS_DIGEST_LEN
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
        poseidon16_compress_half_hardcoded_left_4(input, chain_right, output, first_tweak)
    else:
        digests = Array(n * XMSS_DIGEST_LEN)

        # Hash 0: input → digests[0..4]
        first_tweak = chain_i_tweaks + starting_step * TWEAK_LEN
        poseidon16_compress_half_hardcoded_left_4(input, chain_right, digests, first_tweak)

        # Hashes 1..n-2: digests[(j-1)*4..j*4] → digests[j*4..(j+1)*4]
        for j in unroll(1, n - 1):
            cur_tweak = chain_i_tweaks + (starting_step + j) * TWEAK_LEN
            poseidon16_compress_half_hardcoded_left_4(
                digests + (j - 1) * XMSS_DIGEST_LEN,
                chain_right,
                digests + j * XMSS_DIGEST_LEN,
                cur_tweak,
            )

        # Final hash: digests[(n-2)*4..(n-1)*4] → output
        last_tweak = chain_i_tweaks + (starting_step + n - 1) * TWEAK_LEN
        poseidon16_compress_half_hardcoded_left_4(
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
    poseidon16_compress_hardcoded_left_4(
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
    # New merkle hash layout:
    #   LEFT  = [tweak(2) | 00 | pp(4)]   ← `[tweak(2) | 00]` is read straight from
    #                                       the merkle tweak slot at the compile-time
    #                                       address `merkle_tweaks_chunk + level*TWEAK_LEN`,
    #                                       and `[pp(4)]` from the runtime `public_param`.
    #   RIGHT = [left_child(4) | right_child(4)]   ← packed contiguously in `buf*`
    #
    # Each level's half-output digest is written DIRECTLY into the next level's `buf`
    # at the correct slot (offset 0 if it's the LEFT child of the next level, offset 4
    # if it's the RIGHT child). The OTHER child slot is filled by `hint_xmss_merkle_node`,
    # which the prover supplies in level order — so neither the merkle path nor the
    # public param are ever copied/duplicated inside `do_4_merkle_levels`. The only
    # remaining copy is `state_in` into the level-0 buffer (we don't know `state_in`'s
    # address layout statically across chunk boundaries).
    #
    # `buf1`/`buf2`/`buf3` are over-allocated to 12 elements (instead of 8) so the
    # half-output lookup at the digest still has 8 valid memory cells when the digest
    # lands at offset 4. The trailing 4 cells are vacuous (memory[buf+8..buf+12] = 0
    # in write-once memory; the prover sets the unconstrained trace columns to 0).
    BUF_SIZE_DEST = DIGEST_LEN + (DIGEST_LEN - XMSS_DIGEST_LEN)  # 8 + 4 = 12

    b0 = b % 2
    r1 = (b - b0) / 2
    b1 = r1 % 2
    r2 = (r1 - b1) / 2
    b2 = r2 % 2
    r3 = (r2 - b2) / 2
    b3 = r3 % 2

    # Level 0 input: copy state_in into buf0 (we don't know its address statically);
    # hint the level-0 merkle path neighbour into the OTHER slot.
    #
    # We use copy_5 (1 dot_product_ee precompile call) instead of a 4-write loop in
    # both branches. copy_5 writes 5 FE, and dot_product_ee's runtime helper also
    # READS all 5 source elements via solve_unknowns, so state_in needs an extra
    # readable element on the side opposite the hint slot:
    #   - b0 == 1: copy_5(state_in - 1, buf0 - 1). Source slack at state_in[-1],
    #              destination slack at buf0[-1]. state_in[-1] is initialized by the
    #              previous chunk's `state_out[7] = 0` write (or by `wots_pk_hash`'s
    #              full output for chunk 0, or by the leading-slot init in
    #              `xmss_merkle_verify` for chunk 1).
    #   - b0 == 0: copy_5(state_in, buf0 + 4).     Source slack at state_in[4],
    #              destination slack at buf0[8]. state_in[4] is initialized by the
    #              previous chunk's `state_out[4] = 0` write (or by full output for
    #              chunk 0).
    # buf0 is over-allocated by 2 (one slack at each end) so a single allocation
    # serves both branches.
    buf0_alloc = Array(DIGEST_LEN + 2)  # 10 elements
    buf0 = buf0_alloc + 1  # logical positions [-1..8]
    if b0 == 1:
        # state_in is the LEFT child → state_in[0..4] lands at buf0[0..4].
        copy_5(state_in - 1, buf0 - 1)
        hint_xmss_merkle_node(buf0 + XMSS_DIGEST_LEN)
    else:
        # state_in is the RIGHT child → state_in[0..4] lands at buf0[4..8].
        hint_xmss_merkle_node(buf0)
        copy_5(state_in, buf0 + XMSS_DIGEST_LEN)

    # Level 0 hash → buf1 (digest at offset 0 if LEFT child of level 1, else offset 4).
    # The path neighbour for level 1 is hinted into the OTHER slot of buf1.
    buf1 = Array(BUF_SIZE_DEST)
    if b1 == 1:
        poseidon16_compress_half_hardcoded_left_4(public_param, buf0, buf1, merkle_tweaks_chunk)
        hint_xmss_merkle_node(buf1 + XMSS_DIGEST_LEN)
    else:
        poseidon16_compress_half_hardcoded_left_4(public_param, buf0, buf1 + XMSS_DIGEST_LEN, merkle_tweaks_chunk)
        hint_xmss_merkle_node(buf1)

    # Level 1 hash → buf2
    buf2 = Array(BUF_SIZE_DEST)
    if b2 == 1:
        poseidon16_compress_half_hardcoded_left_4(public_param, buf1, buf2, merkle_tweaks_chunk + 1 * TWEAK_LEN)
        hint_xmss_merkle_node(buf2 + XMSS_DIGEST_LEN)
    else:
        poseidon16_compress_half_hardcoded_left_4(public_param, buf1, buf2 + XMSS_DIGEST_LEN, merkle_tweaks_chunk + 1 * TWEAK_LEN)
        hint_xmss_merkle_node(buf2)

    # Level 2 hash → buf3
    buf3 = Array(BUF_SIZE_DEST)
    if b3 == 1:
        poseidon16_compress_half_hardcoded_left_4(public_param, buf2, buf3, merkle_tweaks_chunk + 2 * TWEAK_LEN)
        hint_xmss_merkle_node(buf3 + XMSS_DIGEST_LEN)
    else:
        poseidon16_compress_half_hardcoded_left_4(public_param, buf2, buf3 + XMSS_DIGEST_LEN, merkle_tweaks_chunk + 2 * TWEAK_LEN)
        hint_xmss_merkle_node(buf3)

    # Level 3 hash → state_out (digest always written at offset 0 since the next chunk
    # reads state_out as a 4-element pointer regardless).
    # The next chunk's level-0 copy_5 reads `state_in[4]` (b0 == 0) or `state_in[-1]`
    # (b0 == 1), which lands in this chunk's `state_out[4]` / `state_out[7]`. These
    # cells are unwritten by this poseidon (half_output only writes [0..4]); the
    # extension_op `solve_unknowns` "copy_5" fast path handles undefined cells
    # cell-by-cell and sets both source/dest to zero — no explicit writes needed.
    poseidon16_compress_half_hardcoded_left_4(public_param, buf3, state_out, merkle_tweaks_chunk + 3 * TWEAK_LEN)
    return


@inline
def xmss_merkle_verify(leaf_digest, merkle_chunks, expected_root, public_param, merkle_tweaks):
    # Stride (XMSS_DIGEST_LEN + 1) = 5 per chunk: 4 digest cells written by the
    # half-output Poseidon + 1 slack cell. The slack cell holds harmless writes
    # from the next chunk's level-0 copy_5 (which reads `state_in[4]` for b0 == 0
    # or `state_in[-1]` for b0 == 1; with stride 5 both reads land in an adjacent
    # chunk's slack cell, never colliding with a written digest cell).
    #
    # Allocation = 1 leading slack + (N-1) chunks × 5 cells + 4 trailing slack (for
    # the LAST stored chunk's half-output Poseidon lookup which reads 8 cells past
    # the storage start) = 5 * N_MERKLE_CHUNKS cells.
    #
    # The leading slack cell does NOT need an explicit `= 0` write — the execute
    # fix in `solve_unknowns` handles undefined source/dest cells via the copy_5
    # fast path by setting both to zero.
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

    # Last chunk: write to a 5-cell buffer (4 digest cells + 1 slack for copy_5).
    last_output = Array(DIM)
    match_range(
        merkle_chunks[N_MERKLE_CHUNKS - 1],
        range(0, 16),
        lambda b: do_4_merkle_levels(
            b,
            state_indexes[N_MERKLE_CHUNKS - 2],
            last_output,
            public_param,
            merkle_tweaks + (N_MERKLE_CHUNKS - 1) * MERKLE_LEVELS_PER_CHUNK * TWEAK_LEN,
        ),
    )

    # Assert computed root == expected (first XMSS_DIGEST elements).
    # Single-cycle copy_5: cells 0..3 verify the digest against the merkle root in
    # `expected_root` (the actual assertion). Cell 4 of `last_output` is undefined
    # (do_4_merkle_levels no longer pre-writes the slack), and cell 4 of expected_root
    # is `public_param[0]` (defined in pub_mem). The extension_op `solve_unknowns`
    # copy_5 fast path handles this cell-by-cell: source unknown + dest known →
    # propagate dest into source. Memory[last_output[4]] gets set to public_param[0],
    # harmless because nothing else reads it.
    copy_5(last_output, expected_root)
    return
