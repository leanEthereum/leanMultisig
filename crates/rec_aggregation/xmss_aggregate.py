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
SIG_SIZE = RANDOMNESS_LEN + (V + LOG_LIFETIME) * DIGEST_LEN
# Goldilocks encoding: 3 Poseidon8 output FE, each decomposed into CHUNKS_PER_FE
# chunks of W bits. We assume ~64 bits of uniform entropy per FE and consume
# CHUNKS_PER_FE*W = 63 bits per FE (1-bit remainder). 3*21 = 63 total chunks,
# of which the first V+V_GRINDING are the Winternitz indices. Must match
# `crates/xmss/src/wots.rs::wots_encode`.
NUM_ENCODING_FE = 3
CHUNKS_PER_FE = 21
MERKLE_LEVELS_PER_CHUNK = MERKLE_LEVELS_PER_CHUNK_PLACEHOLDER
N_MERKLE_CHUNKS = LOG_LIFETIME / MERKLE_LEVELS_PER_CHUNK


@inline
def xmss_verify(merkle_root, message, slot_lo, slot_hi, merkle_chunks):
    # signature: randomness | chain_tips | merkle_path
    # return the hashed xmss public key
    signature = Array(SIG_SIZE)
    hint_witness("xmss_signature", signature)
    randomness = signature
    chain_starts = signature + RANDOMNESS_LEN
    merkle_path = chain_starts + V * DIGEST_LEN

    # 1) Hash (message, randomness, slot, merkle_root) into 3 output FE via a
    #    3-call Poseidon8 sponge chain, mirroring `poseidon_compress_slice` on
    #    14 input FE in the Rust side.
    #
    # Call 1: poseidon8(message[0..4], randomness[0..4]) → a
    a = Array(DIGEST_LEN)
    poseidon8_compress(message, randomness, a)

    # Call 2: poseidon8(a, [slot_lo, slot_hi, root[0], root[1]]) → b
    rhs2 = Array(DIGEST_LEN)
    rhs2[0] = slot_lo
    rhs2[1] = slot_hi
    rhs2[2] = merkle_root[0]
    rhs2[3] = merkle_root[1]
    b = Array(DIGEST_LEN)
    poseidon8_compress(a, rhs2, b)

    # Call 3: poseidon8(b, [root[2], root[3], 0, 0]) → encoding_fe (4 FE; we use the first 3)
    rhs3 = Array(DIGEST_LEN)
    rhs3[0] = merkle_root[2]
    rhs3[1] = merkle_root[3]
    rhs3[2] = 0
    rhs3[3] = 0
    encoding_fe = Array(DIGEST_LEN)
    poseidon8_compress(b, rhs3, encoding_fe)

    # 2) Decompose each of the first 3 FE into 21 3-bit chunks = 63 bits per FE
    #    (1-bit remainder). 3 × 21 = 63 total chunks; first V+V_GRINDING used.
    encoding = Array(63)
    hint_decompose_bits_xmss(encoding, encoding_fe, 3, 21, W)

    # Each chunk must be a valid W-bit Winternitz index.
    for i in unroll(0, 63):
        assert encoding[i] < CHAIN_LENGTH

    # For each FE: partial_sum = Σ_j encoding[i*K+j] * 2^(W*j) is the low 63
    # bits of encoding_fe[i]; the remainder is a single bit. Factorise the
    # remainder equality so no inverse is needed:
    #   (encoding_fe[i] − partial_sum) · (encoding_fe[i] − partial_sum − 2^63) == 0
    for i in unroll(0, 3):
        partial_sum: Mut = encoding[i * 21]
        for j in unroll(1, 21):
            partial_sum += encoding[i * 21 + j] * (CHAIN_LENGTH ** j)
        diff = encoding_fe[i] - partial_sum
        assert diff * (diff - 2**63) == 0

    # Grinding: last V_GRINDING indices must each be CHAIN_LENGTH - 1.
    for i in unroll(V, V + V_GRINDING):
        assert encoding[i] == CHAIN_LENGTH - 1

    # 3) Chain-hash each of the V WOTS secret-key tips.
    target_sum: Mut = 0
    wots_public_key = Array(V * DIGEST_LEN)
    local_zero_buff = Array(DIGEST_LEN)
    set_to_8_zeros(local_zero_buff)

    for i in unroll(0, V):
        chain_start = chain_starts + i * DIGEST_LEN
        chain_end = wots_public_key + i * DIGEST_LEN
        chain_length_ptr = Array(1)
        match_range(
            encoding[i], range(0, CHAIN_LENGTH),
            lambda n: chain_hash(chain_start, n, chain_end, chain_length_ptr, local_zero_buff),
        )
        target_sum += chain_length_ptr[0]

    assert target_sum == TARGET_SUM

    wots_pubkey_hashed = slice_hash(wots_public_key, V)

    xmss_merkle_verify(wots_pubkey_hashed, merkle_path, merkle_chunks, merkle_root)

    return


@inline
def chain_hash(input_ptr, n, output_ptr, chain_length_ptr, local_zero_buff):
    # Iterate the WOTS chain hash `n_hashes = (CHAIN_LENGTH-1) - n` times, starting
    # from the signer's chain tip at `input_ptr`, producing `output_ptr`. Records
    # `n` in `chain_length_ptr[0]` so the caller can accumulate the target sum.
    debug_assert(n < CHAIN_LENGTH)

    n_hashes = (CHAIN_LENGTH - 1) - n
    if n_hashes == 0:
        copy_8(input_ptr, output_ptr)
    elif n_hashes == 1:
        poseidon8_compress(input_ptr, local_zero_buff, output_ptr)
    else:
        states = Array((n_hashes - 1) * DIGEST_LEN)
        poseidon8_compress(input_ptr, local_zero_buff, states)
        for i in unroll(1, n_hashes - 1):
            poseidon8_compress(states + (i - 1) * DIGEST_LEN, local_zero_buff, states + i * DIGEST_LEN)
        poseidon8_compress(states + (n_hashes - 2) * DIGEST_LEN, local_zero_buff, output_ptr)

    chain_length_ptr[0] = n

    return


@inline
def do_4_merkle_levels(b, state_in, path_chunk, state_out):
    # Extract bits of b (compile-time; each division is exact so field div == integer div)
    b0 = b % 2
    r1 = (b - b0) / 2
    b1 = r1 % 2
    r2 = (r1 - b1) / 2
    b2 = r2 % 2
    r3 = (r2 - b2) / 2
    b3 = r3 % 2

    temps = Array(3 * DIGEST_LEN)

    # Level 0: state_in -> temps
    if b0 == 0:
        poseidon8_compress(path_chunk, state_in, temps)
    else:
        poseidon8_compress(state_in, path_chunk, temps)

    # Level 1
    if b1 == 0:
        poseidon8_compress(path_chunk + 1 * DIGEST_LEN, temps, temps + DIGEST_LEN)
    else:
        poseidon8_compress(temps, path_chunk + 1 * DIGEST_LEN, temps + DIGEST_LEN)

    # Level 2
    if b2 == 0:
        poseidon8_compress(path_chunk + 2 * DIGEST_LEN, temps + DIGEST_LEN, temps + 2 * DIGEST_LEN)
    else:
        poseidon8_compress(temps + DIGEST_LEN, path_chunk + 2 * DIGEST_LEN, temps + 2 * DIGEST_LEN)

    # Level 3: -> state_out
    if b3 == 0:
        poseidon8_compress(path_chunk + 3 * DIGEST_LEN, temps + 2 * DIGEST_LEN, state_out)
    else:
        poseidon8_compress(temps + 2 * DIGEST_LEN, path_chunk + 3 * DIGEST_LEN, state_out)
    return


@inline
def xmss_merkle_verify(leaf_digest, merkle_path, merkle_chunks, expected_root):
    states = Array((N_MERKLE_CHUNKS - 1) * DIGEST_LEN)

    # First chunk: leaf_digest -> states
    match_range(merkle_chunks[0], range(0, 16), lambda b: do_4_merkle_levels(b, leaf_digest, merkle_path, states))

    # Middle chunks
    for j in unroll(1, N_MERKLE_CHUNKS - 1):
        match_range(
            merkle_chunks[j],
            range(0, 16),
            lambda b: do_4_merkle_levels(
                b, states + (j - 1) * DIGEST_LEN, merkle_path + j * MERKLE_LEVELS_PER_CHUNK * DIGEST_LEN, states + j * DIGEST_LEN
            ),
        )

    # Last chunk: -> expected_root
    match_range(
        merkle_chunks[N_MERKLE_CHUNKS - 1],
        range(0, 16),
        lambda b: do_4_merkle_levels(
            b, states + (N_MERKLE_CHUNKS - 2) * DIGEST_LEN, merkle_path + (N_MERKLE_CHUNKS - 1) * MERKLE_LEVELS_PER_CHUNK * DIGEST_LEN, expected_root
        ),
    )
    return


@inline
def copy_7(x, y):
    dot_product_ee(x, ONE_EF_PTR, y)
    dot_product_ee(x + (7 - DIM), ONE_EF_PTR, y + (7 - DIM))
    return


@inline
def copy_6(x, y):
    dot_product_ee(x, ONE_EF_PTR, y)
    y[DIM] = x[DIM]
    return
