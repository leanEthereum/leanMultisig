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
    _, sampled_low_bits_value = checked_decompose_bits(sampled, bits)
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


def fs_receive_ef(fs, n: Const):
    new_fs, ef_ptr = fs_receive_chunks(fs, div_ceil(n * DIM, 8))
    for i in unroll(n * DIM, next_multiple_of(n * DIM, 8)):
        assert ef_ptr[i] == 0
    return new_fs, ef_ptr


def fs_print_state(fs_state):
    for i in unroll(0, 9):
        print(i, fs_state[i])
    return


def sample_bits_const(fs, n_samples: Const, K):
    # return the updated fiat-shamir, and a pointer to n pointers, each pointing to 31 (boolean) field elements,
    sampled_bits = Array(n_samples)
    n_chunks = div_ceil(n_samples, 8)
    new_fs, sampled = fs_sample_chunks(fs, n_chunks)
    for i in unroll(0, n_samples):
        bits, _ = checked_decompose_bits(sampled[i], K)
        sampled_bits[i] = bits
    return new_fs, sampled_bits


def sample_bits_dynamic(fs_state, n_samples, K):
    new_fs_state: Imu
    sampled_bits: Imu
    for r in unroll(0, N_ROUNDS_BASE + 1):
        if n_samples == NUM_QUERIES_BASE[r]:
            new_fs_state, sampled_bits = sample_bits_const(fs_state, NUM_QUERIES_BASE[r], K)
            return new_fs_state, sampled_bits
    for r in unroll(0, N_ROUNDS_EXT + 1):
        if n_samples == NUM_QUERIES_EXT[r]:
            new_fs_state, sampled_bits = sample_bits_const(fs_state, NUM_QUERIES_EXT[r], K)
            return new_fs_state, sampled_bits
    assert False, "sample_bits_dynamic called with unsupported n_samples"
