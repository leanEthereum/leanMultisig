from snark_lib import *
# FIAT SHAMIR layout: 17 field elements
# 0..8 -> first half of sponge state
# 8 -> transcript pointer

from utils import *


def fs_new(transcript_ptr):
    fs_state = Array(9)
    set_to_8_zeros(fs_state)
    fs_state[8] = transcript_ptr
    return fs_state


def fs_absorb(fs, data, length: Const):
    # Absorb `length` continuous field elements into the sponge, 7 per Poseidon
    # permutation. Permutation k compresses [-1, data[7k .. 7k+7]] with the
    # running state (last permutation zero-padded). The leading -1 domain-
    # separates absorption from fs_sample_*, which use separators 0..=n in that
    # same slot. `data` itself is left untouched and continuous; we copy it
    # 7-by-7 into fresh `-1`-prefixed scratch chunks.
    debug_assert(length != 0)
    n_perms = div_ceil(length, 7)
    chunks = Array(8 * n_perms)
    for k in unroll(0, n_perms):
        chunks[8 * k] = 0 - 1
    for i in unroll(0, length):
        chunks[8 * div_floor(i, 7) + 1 + (i % 7)] = data[i]
    for i in unroll(length, 7 * n_perms):
        chunks[8 * div_floor(i, 7) + 1 + (i % 7)] = 0
    # Chain the permutations: states[8k .. 8k+8] is the state after permutation k.
    states = Array(8 * n_perms + 1)
    poseidon16_compress(chunks, fs, states)
    for k in unroll(1, n_perms):
        poseidon16_compress(chunks + 8 * k, states + 8 * (k - 1), states + 8 * k)
    return states + 8 * (n_perms - 1)


def fs_observe(fs, data, length: Const):
    new_fs = fs_absorb(fs, data, length)
    new_fs[8] = fs[8]  # preserve transcript pointer
    return new_fs


def fs_receive(fs, length: Const):
    # Absorb `length` continuous elements from the transcript and advance the
    # transcript pointer past them. Returns the updated fs and a pointer to the
    # (continuous, untouched) received data.
    transcript_ptr = fs[8]
    new_fs = fs_absorb(fs, transcript_ptr, length)
    new_fs[8] = transcript_ptr + length
    return new_fs, transcript_ptr


def fs_grinding(fs, bits):
    if bits == 0:
        return fs  # no grinding
    new_fs, _ = fs_receive(fs, 1)  # absorb the grinding witness (1 field element)
    sampled = new_fs[0]
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
    


def fs_sample_chunks(fs, n_chunks: Const):
    # return the updated fiat-shamir, and a pointer to n_chunks chunks of 8 field elements

    sampled = Array((n_chunks + 1) * 8 + 1)
    for i in unroll(0, (n_chunks + 1)):
        domain_sep = Array(8)
        domain_sep[0] = i
        set_to_7_zeros(domain_sep + 1)
        poseidon16_compress(
            domain_sep,
            fs,
            sampled + i * 8,
        )
    sampled[(n_chunks + 1) * 8] = fs[8]  # same transcript pointer
    new_fs = sampled + n_chunks * 8
    return new_fs, sampled


@inline
def fs_sample_ef(fs):
    sampled = Array(8)
    poseidon16_compress(ZERO_VEC_PTR, fs, sampled)
    new_fs = Array(9)
    poseidon16_compress(SAMPLING_DOMAIN_SEPARATOR_PTR, fs, new_fs)
    new_fs[8] = fs[8]  # same transcript pointer
    return new_fs, sampled


def fs_sample_many_ef(fs, n):
    # return the updated fiat-shamir, and a pointer to n (continuous) extension field elements
    n_chunks = div_ceil_dynamic(n * DIM, 8)
    debug_assert(n_chunks <= 31)
    debug_assert(1 <= n_chunks)
    new_fs, sampled = match_range(n_chunks, range(1, 32), lambda nc: fs_sample_chunks(fs, nc))
    return new_fs, sampled


@inline
def fs_hint(fs, n):
    # return the updated fiat-shamir, and a pointer to n field elements from the transcript
    transcript_ptr = fs[8]
    new_fs = Array(9)
    copy_8(fs, new_fs)
    new_fs[8] = fs[8] + n  # advance transcript pointer
    return new_fs, transcript_ptr


def fs_receive_chunks(fs, n_chunks: Const):
    # each chunk = 8 field elements (e.g. a digest)
    new_fs, transcript_ptr = fs_receive(fs, 8 * n_chunks)
    return new_fs, transcript_ptr


@inline
def fs_receive_ef_inlined(fs, n):
    new_fs, ef_ptr = fs_receive(fs, n * DIM)
    return new_fs, ef_ptr


def fs_receive_ef_by_log_dynamic(fs, log_n, min_value: Const, max_value: Const):
    debug_assert(log_n < max_value)
    debug_assert(min_value <= log_n)
    new_fs: Imu
    ef_ptr: Imu
    new_fs, ef_ptr = match_range(log_n, range(min_value, max_value), lambda ln: fs_receive_ef(fs, 2**ln))
    return new_fs, ef_ptr


def fs_receive_ef(fs, n: Const):
    new_fs, ef_ptr = fs_receive(fs, n * DIM)
    return new_fs, ef_ptr


def fs_print_state(fs_state):
    for i in unroll(0, 9):
        print(i, fs_state[i])
    return


def fs_sample_data_with_offset(fs, n_chunks: Const, offset):
    # Like fs_sample_chunks but uses domain separators [offset..offset+n_chunks-1].
    # Only returns the sampled data, does NOT update fs.
    sampled = Array(n_chunks * 8)
    for i in unroll(0, n_chunks):
        domain_sep = Array(8)
        domain_sep[0] = offset + i
        set_to_7_zeros(domain_sep + 1)
        poseidon16_compress(domain_sep, fs, sampled + i * 8)
    return sampled


def fs_finalize_sample(fs, total_n_chunks):
    # Compute new fs state using domain_sep = total_n_chunks
    # (same as the last poseidon call in fs_sample_chunks).
    new_fs = Array(9)
    domain_sep = Array(8)
    domain_sep[0] = total_n_chunks
    set_to_7_zeros(domain_sep + 1)
    poseidon16_compress(domain_sep, fs, new_fs)
    new_fs[8] = fs[8]  # same transcript pointer
    return new_fs


@inline
def fs_sample_queries(fs, n_samples):
    debug_assert(n_samples < 512)
    # Compute total_chunks = ceil(n_samples / 8) via bit decomposition.
    # Big-endian: nb[0]=bit8 (MSB), nb[8]=bit0 (LSB).
    nb = checked_decompose_bits_small_value_const(n_samples, 9)
    floor_div = nb[0] * 32 + nb[1] * 16 + nb[2] * 8 + nb[3] * 4 + nb[4] * 2 + nb[5]
    has_remainder = 1 - (1 - nb[6]) * (1 - nb[7]) * (1 - nb[8])
    total_chunks = floor_div + has_remainder
    # Sample exactly the needed chunks (dispatch via match_range to keep n_chunks const)
    sampled = match_range(total_chunks, range(0, 65), lambda nc: fs_sample_data_with_offset(fs, nc, 0))
    new_fs = fs_finalize_sample(fs, total_chunks)
    return sampled, new_fs
