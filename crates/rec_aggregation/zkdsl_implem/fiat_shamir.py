from snark_lib import *
from utils import *


# fs layout (17 cells):
#   fs[0..8]   = capacity
#   fs[8..16]  = rate
#   fs[16]     = transcript pointer
# This matches the normal-ordering poseidon precompile output [cap | rate].


def fs_new(transcript_ptr):
    fs = Array(17)
    set_to_16_zeros(fs)
    fs[16] = transcript_ptr
    return fs


@inline
def _absorb_chunks(fs, data, n_chunks, new_transcript_ptr):
    assert n_chunks != 0
    chain = Array(n_chunks * 16 + 1)
    poseidon16_permute(fs, data, chain)
    for i in unroll(1, n_chunks):
        poseidon16_permute(chain + (i - 1) * 16, data + i * DIGEST_LEN, chain + i * 16)
    chain[n_chunks * 16] = new_transcript_ptr
    return chain + (n_chunks - 1) * 16


@inline
def fs_observe_chunks(fs, data, n_chunks):
    return _absorb_chunks(fs, data, n_chunks, fs[16])


def fs_observe(fs, data, length: Const):
    n_full_chunks = (length - (length % DIGEST_LEN)) / DIGEST_LEN
    remainder = length % DIGEST_LEN
    if remainder == 0:
        return fs_observe_chunks(fs, data, n_full_chunks)
    intermediate = fs_observe_chunks(fs, data, n_full_chunks)
    padded = Array(DIGEST_LEN)
    for j in unroll(0, remainder):
        padded[j] = data[n_full_chunks * DIGEST_LEN + j]
    for j in unroll(remainder, DIGEST_LEN):
        padded[j] = 0
    return fs_observe_chunks(intermediate, padded, 1)


def fs_grinding(fs, bits):
    if bits == 0:
        return fs  # no grinding
    transcript_ptr = fs[16]
    new_fs = _absorb_chunks(fs, transcript_ptr, 1, transcript_ptr + DIGEST_LEN)

    # Rate is at new_fs[8..16]; sample the first cell of it for the grinding check.
    sampled = new_fs[8]
    debug_assert(bits <= 24)
    match_range(bits, range(0, 25), lambda b: assert_trailing_bits_are_zeros(sampled, b))

    return new_fs


def assert_trailing_bits_are_zeros(value, bits: Const):
    debug_assert(bits != 0)

    chunk_size = 12
    num_chunks = 24 / chunk_size # 2

    chunks = Array(num_chunks)
    hint_decompose_bits_merkle_whir(chunks, value, chunk_size)
    for i in unroll(0, num_chunks):
        assert chunks[i] < 2**chunk_size

    partial_sums = Array(num_chunks)
    partial_sums[0] = chunks[0]
    for i in unroll(1, num_chunks):
        partial_sums[i] = partial_sums[i - 1] + chunks[i] * 2**(i * chunk_size)
    # p = 2^31 - 2^24 + 1, so 2^24 * 127 = p - 1 ≡ -1 (mod p), hence inv(2^24) = -127.
    # Deduce top7 from the identity partial_sum + top7 * 2^24 == a:
    # top7 = (a - partial_sum) * inv(2^24) = (partial_sum - a) * 127
    top7 = (partial_sums[num_chunks - 1] - value) * 127
    assert top7 < 2**7
    if top7 == 2**7 - 1:
        assert partial_sums[chunk_size - 1] == 0

    if bits < 12:
        assert chunks[0] / 2**bits < 2**(chunk_size - bits)
    elif bits < 24:
        assert chunks[0] == 0
        assert chunks[1] / 2**(bits - 12) < 2**(chunk_size - (bits - 12))
    else:
        debug_assert(bits == 24)
        assert chunks[0] == 0
        assert chunks[1] == 0

    return


@inline
def fs_duplex(fs):
    # (equivalent to absorbing 8 zeros)
    # Refreshes the rate so a subsequent sample doesn't repeat the previous one.
    new_fs = Array(17)
    poseidon16_permute(fs, ZERO_VEC_PTR, new_fs)
    new_fs[16] = fs[16]
    return new_fs


def fs_sample_chunks(fs, n_chunks: Const):
    # Returns (new_fs, samples_ptr) where samples_ptr points to a contiguous
    # n_chunks * 8-cell buffer holding the squeezed chunks. Assumes the rate at
    # fs[8..16] is "fresh" (just-permuted, not yet emitted); caller must duplex
    # (or observe) between independent sample sequences.
    if n_chunks == 0:
        return fs, ZERO_VEC_PTR
    if n_chunks == 1:
        # Chunk 0 is the current fs itself: its rate is fs[8..16], no permute needed.
        return fs, fs + 8
    samples = Array(n_chunks * 8)
    copy_8(samples, fs + 8)
    chain = Array((n_chunks - 1) * 16 + 1)
    poseidon16_permute(fs, ZERO_VEC_PTR, chain)
    copy_8(samples + 8, chain + 8)
    for i in unroll(2, n_chunks):
        poseidon16_permute(chain + (i - 2) * 16, ZERO_VEC_PTR, chain + (i - 1) * 16)
        copy_8(samples + i * 8, chain + (i - 1) * 16 + 8)
    chain[(n_chunks - 1) * 16] = fs[16]
    new_fs = chain + (n_chunks - 2) * 16
    return new_fs, samples


@inline
def fs_sample_ef(fs):
    # Single-chunk sample: read the fresh rate at fs[8..16]; the new fs is unchanged.
    return fs, fs + 8


@inline
def fs_sample_many_ef(fs, n):
    # return the updated fiat-shamir, and a pointer to n (continuous) extension field elements
    n_chunks = div_ceil(n * DIM, 8)
    debug_assert(n_chunks <= 31)
    debug_assert(1 <= n_chunks)
    new_fs, sampled = fs_sample_chunks(fs, n_chunks)
    return new_fs, sampled


@inline
def fs_hint(fs, n):
    # Hint = read `n` cells from the transcript without absorbing them. Just advance the
    # transcript pointer; the sponge state is unchanged.
    new_fs = Array(17)
    copy_8(new_fs, fs)
    copy_8(new_fs + 8, fs + 8)
    new_fs[16] = fs[16] + n
    return new_fs, fs[16]


def fs_receive_chunks(fs, n_chunks: Const):
    # Read n_chunks * 8 cells from the transcript and absorb them. Returns the new fs
    # and a pointer to the just-consumed transcript region.
    transcript_ptr = fs[16]
    new_fs = _absorb_chunks(fs, transcript_ptr, n_chunks, transcript_ptr + n_chunks * DIGEST_LEN)
    return new_fs, transcript_ptr


@inline
def fs_receive_ef_inlined(fs, n):
    new_fs, ef_ptr = fs_receive_chunks(fs, div_ceil(n * DIM, 8))
    for i in unroll(n * DIM, next_multiple_of(n * DIM, 8)):
        assert ef_ptr[i] == 0
    return new_fs, ef_ptr


def fs_receive_ef_by_log_dynamic(fs, log_n, min_value: Const, max_value: Const):
    debug_assert(log_n < max_value)
    debug_assert(min_value <= log_n)
    new_fs: Imu
    ef_ptr: Imu
    new_fs, ef_ptr = match_range(log_n, range(min_value, max_value), lambda ln: fs_receive_ef(fs, 2**ln))
    return new_fs, ef_ptr


def fs_receive_ef(fs, n: Const):
    new_fs, ef_ptr = fs_receive_chunks(fs, div_ceil(n * DIM, 8))
    for i in unroll(n * DIM, next_multiple_of(n * DIM, 8)):
        assert ef_ptr[i] == 0
    return new_fs, ef_ptr


def fs_print_state(fs_state):
    for i in unroll(0, 17):
        print(i, fs_state[i])
    return


@inline
def fs_sample_queries(fs, n_samples):
    # Sample `n_samples` query bit-strings. Each chunk yields 8 base field elements that
    # can be downsampled to query indices. We squeeze `ceil(n_samples / 8)` chunks.
    debug_assert(n_samples < 512)
    # Compute total_chunks = ceil(n_samples / 8) via bit decomposition.
    # Big-endian: nb[0]=bit8 (MSB), nb[8]=bit0 (LSB).
    nb = checked_decompose_bits_small_value_const(n_samples, 9)
    floor_div = nb[0] * 32 + nb[1] * 16 + nb[2] * 8 + nb[3] * 4 + nb[4] * 2 + nb[5]
    has_remainder = 1 - (1 - nb[6]) * (1 - nb[7]) * (1 - nb[8])
    total_chunks = floor_div + has_remainder
    new_fs, sampled = match_range(total_chunks, range(0, 65), lambda nc: fs_sample_chunks(fs, nc))
    return sampled, new_fs
