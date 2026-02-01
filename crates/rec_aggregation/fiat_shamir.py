from snark_lib import *
# FIAT SHAMIR layout: 17 field elements
# 0..8 -> first half of sponge state
# 8..16 -> second half of sponge state
# 16 -> transcript pointer

from utils import *


def fs_new(transcript_ptr):
    fs_state = Array(17)
    set_to_16_zeros(fs_state)
    fs_state[16] = transcript_ptr
    duplexed = duplexing(fs_state)
    return duplexed


def duplexing(fs):
    new_fs = Array(17)
    poseidon16(fs, fs + 8, new_fs, PERMUTATION)
    new_fs[16] = fs[16]
    return new_fs


def fs_grinding(fs, bits):
    if bits == 0:
        return fs  # no grinding
    left = Array(8)
    grinding_witness = read_memory(fs[16])
    left[0] = grinding_witness
    set_to_7_zeros(left + 1)

    fs_after_poseidon = Array(17)
    poseidon16(left, fs + 8, fs_after_poseidon, PERMUTATION)
    fs_after_poseidon[16] = fs[16] + 1  # one element read from transcript

    sampled = fs_after_poseidon[0]
    _, sampled_low_bits_value = checked_decompose_bits(sampled, bits)
    assert sampled_low_bits_value == 0

    fs_duplexed = duplexing(fs_after_poseidon)

    return fs_duplexed


def fs_sample_ef(fs):
    return fs


def fs_hint(fs, n):
    # return the updated fiat-shamir, and a pointer to n field elements from the transcript

    transcript_ptr = fs[16]
    new_fs = Array(17)
    copy_16(fs, new_fs)
    new_fs[16] = fs[16] + n  # advance transcript pointer
    return new_fs, transcript_ptr


def fs_receive_chunks(fs, n_chunks: Const):
    # each chunk = 8 field elements
    new_fs = Array(1 + 16 * n_chunks)
    transcript_ptr = fs[16]
    new_fs[16 * n_chunks] = transcript_ptr + 8 * n_chunks  # advance transcript pointer

    poseidon16(transcript_ptr, fs + 8, new_fs, PERMUTATION)
    for i in unroll(1, n_chunks):
        poseidon16(
            transcript_ptr + i * 8,
            new_fs + ((i - 1) * 16 + 8),
            new_fs + i * 16,
            PERMUTATION,
        )
    return new_fs + 16 * (n_chunks - 1), transcript_ptr


def fs_receive_ef(fs, n: Const):
    new_fs, ef_ptr = fs_receive_chunks(fs, next_multiple_of(n * DIM, 8) / 8)
    for i in unroll(n * DIM, next_multiple_of(n * DIM, 8)):
        assert ef_ptr[i] == 0
    return new_fs, ef_ptr


def fs_print_state(fs_state):
    for i in unroll(0, 17):
        print(i, fs_state[i])
    return


def sample_bits_const(fs: Mut, n_samples: Const, K):
    # return the updated fiat-shamir, and a pointer to n pointers, each pointing to 31 (boolean) field elements,
    sampled_bits = Array(n_samples)
    for i in unroll(0, (next_multiple_of(n_samples, 8) / 8) - 1):
        for j in unroll(0, 8):
            bits, _ = checked_decompose_bits(fs[j], K)
            sampled_bits[i * 8 + j] = bits
        fs = duplexing(fs)
    # Last batch (may be partial)
    for j in unroll(0, 8 - ((8 - (n_samples % 8)) % 8)):
        bits, _ = checked_decompose_bits(fs[j], K)
        sampled_bits[((next_multiple_of(n_samples, 8) / 8) - 1) * 8 + j] = bits
    return duplexing(fs), sampled_bits


def sample_bits_dynamic(fs_state, n_samples, K):
    new_fs_state: Imu
    sampled_bits: Imu
    for r in unroll(0, WHIR_N_ROUNDS + 1):
        if n_samples == WHIR_NUM_QUERIES[r]:
            new_fs_state, sampled_bits = sample_bits_const(fs_state, WHIR_NUM_QUERIES[r], K)
            return new_fs_state, sampled_bits
    assert False, "sample_bits_dynamic called with unsupported n_samples"
