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


def fs_grinding(fs, bits):
    if bits == 0:
        return fs  # no grinding
    transcript_ptr = fs[8]
    set_to_7_zeros(transcript_ptr + 1)

    new_fs = Array(9)
    poseidon16(fs, transcript_ptr, new_fs)
    new_fs[8] = transcript_ptr + 8

    sampled = new_fs[0]
    _, partial_sums_24 = checked_decompose_bits(sampled)
    sampled_low_bits_value = partial_sums_24[bits - 1]
    assert sampled_low_bits_value == 0

    return new_fs


def fs_sample_chunks(fs, n_chunks: Const):
    # return the updated fiat-shamir, and a pointer to n_chunks chunks of 8 field elements

    sampled = Array((n_chunks + 1) * 8 + 1)
    for i in unroll(0, (n_chunks + 1)):
        domain_sep = Array(8)
        domain_sep[0] = i
        set_to_7_zeros(domain_sep + 1)
        poseidon16(
            fs,
            domain_sep,
            sampled + i * 8,
        )
    sampled[(n_chunks + 1) * 8] = fs[8]  # same transcript pointer
    new_fs = sampled + n_chunks * 8
    return new_fs, sampled


@inline
def fs_sample_ef(fs):
    sampled = Array(8)
    poseidon16(fs, ZERO_VEC_PTR, sampled)
    new_fs = Array(9)
    poseidon16(fs, SAMPLING_DOMAIN_SEPARATOR_PTR, new_fs)
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
    # each chunk = 8 field elements
    new_fs = Array(1 + 8 * n_chunks)
    transcript_ptr = fs[8]
    new_fs[8 * n_chunks] = transcript_ptr + 8 * n_chunks  # advance transcript pointer

    poseidon16(fs, transcript_ptr, new_fs)
    for i in unroll(1, n_chunks):
        poseidon16(
            new_fs + ((i - 1) * 8),
            transcript_ptr + i * 8,
            new_fs + i * 8,
        )
    return new_fs + 8 * (n_chunks - 1), transcript_ptr


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
        poseidon16(fs, domain_sep, sampled + i * 8)
    return sampled


def fs_finalize_sample(fs, total_n_chunks):
    # Compute new fs state using domain_sep = total_n_chunks
    # (same as the last poseidon call in fs_sample_chunks).
    new_fs = Array(9)
    domain_sep = Array(8)
    domain_sep[0] = total_n_chunks
    set_to_7_zeros(domain_sep + 1)
    poseidon16(fs, domain_sep, new_fs)
    new_fs[8] = fs[8]  # same transcript pointer
    return new_fs


def sample_bits_dynamic(fs: Mut, n_samples):
    debug_assert(n_samples < 256)
    # Compute total_chunks = ceil(n_samples / 8) via bit decomposition.
    # Big-endian: nb[0]=bit7 (MSB), nb[7]=bit0 (LSB).
    nb = checked_decompose_bits_small_value_const(n_samples, 8)
    floor_div = nb[0]*16 + nb[1]*8 + nb[2]*4 + nb[3]*2 + nb[4]
    has_remainder = 1 - (1 - nb[5]) * (1 - nb[6]) * (1 - nb[7])
    total_chunks = floor_div + has_remainder
    # Sample exactly the needed chunks (dispatch via match_range to keep n_chunks const)
    sampled = match_range(total_chunks, range(0, 33), lambda nc: fs_sample_data_with_offset(fs, nc, 0))
    # Decompose each sampled field element into bits
    sampled_bits = Array(n_samples)
    for i in dynamic_unroll(0, n_samples, 8):
        bits, _ = checked_decompose_bits(sampled[i])
        sampled_bits[i] = bits
    new_fs = fs_finalize_sample(fs, total_chunks)
    return new_fs, sampled_bits