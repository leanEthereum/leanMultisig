from snark_lib import *

# FIAT SHAMIR layout (Goldilocks, DIGEST_LEN=4): 1 + DIGEST_LEN field elements
#   slots 0..DIGEST_LEN   → sponge state (one digest)
#   slot  DIGEST_LEN      → transcript pointer

from utils import *


FS_SIZE = DIGEST_LEN + 1
FS_TPTR = DIGEST_LEN  # index of transcript pointer inside an FS state


def fs_new(transcript_ptr):
    fs_state = Array(FS_SIZE)
    zero_digest(fs_state)
    fs_state[FS_TPTR] = transcript_ptr
    return fs_state


@inline
def fs_observe_chunks(fs, data, n_chunks):
    result: Mut = Array(FS_SIZE)
    poseidon8_compress(fs, data, result)
    for i in unroll(1, n_chunks):
        new_result = Array(FS_SIZE)
        poseidon8_compress(result, data + i * DIGEST_LEN, new_result)
        result = new_result
    result[FS_TPTR] = fs[FS_TPTR]  # preserve transcript pointer
    return result


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
    final_result = Array(FS_SIZE)
    poseidon8_compress(intermediate, padded, final_result)
    final_result[FS_TPTR] = fs[FS_TPTR]  # preserve transcript pointer
    return final_result


def fs_grinding(fs, bits):
    if bits == 0:
        return fs  # no grinding
    transcript_ptr = fs[FS_TPTR]
    zero_digest_tail(transcript_ptr + 1)

    new_fs = Array(FS_SIZE)
    poseidon8_compress(fs, transcript_ptr, new_fs)
    new_fs[FS_TPTR] = transcript_ptr + DIGEST_LEN

    sampled = new_fs[0]
    _, partial_sums_24 = checked_decompose_bits(sampled)
    sampled_low_bits_value = partial_sums_24[bits - 1]
    assert sampled_low_bits_value == 0

    return new_fs


def fs_sample_chunks(fs, n_chunks: Const):
    # return the updated fiat-shamir, and a pointer to n_chunks chunks of DIGEST_LEN field elements

    sampled = Array((n_chunks + 1) * DIGEST_LEN + 1)
    for i in unroll(0, (n_chunks + 1)):
        domain_sep = Array(DIGEST_LEN)
        domain_sep[0] = i
        zero_digest_tail(domain_sep + 1)
        poseidon8_compress(
            domain_sep,
            fs,
            sampled + i * DIGEST_LEN,
        )
    sampled[(n_chunks + 1) * DIGEST_LEN] = fs[FS_TPTR]  # same transcript pointer
    new_fs = sampled + n_chunks * DIGEST_LEN
    return new_fs, sampled


@inline
def fs_sample_ef(fs):
    sampled = Array(DIGEST_LEN)
    poseidon8_compress(ZERO_VEC_PTR, fs, sampled)
    new_fs = Array(FS_SIZE)
    poseidon8_compress(SAMPLING_DOMAIN_SEPARATOR_PTR, fs, new_fs)
    new_fs[FS_TPTR] = fs[FS_TPTR]  # same transcript pointer
    return new_fs, sampled


def fs_sample_many_ef(fs, n):
    # return the updated fiat-shamir, and a pointer to n (continuous) extension field elements
    n_chunks = div_ceil_dynamic(n * DIM, DIGEST_LEN)
    debug_assert(n_chunks <= 31)
    debug_assert(1 <= n_chunks)
    new_fs, sampled = match_range(n_chunks, range(1, 32), lambda nc: fs_sample_chunks(fs, nc))
    return new_fs, sampled


@inline
def fs_hint(fs, n):
    # return the updated fiat-shamir, and a pointer to n field elements from the transcript
    transcript_ptr = fs[FS_TPTR]
    new_fs = Array(FS_SIZE)
    copy_digest(fs, new_fs)
    new_fs[FS_TPTR] = fs[FS_TPTR] + n  # advance transcript pointer
    return new_fs, transcript_ptr


def fs_receive_chunks(fs, n_chunks: Const):
    # each chunk = DIGEST_LEN field elements
    new_fs = Array(1 + DIGEST_LEN * n_chunks)
    transcript_ptr = fs[FS_TPTR]
    new_fs[DIGEST_LEN * n_chunks] = transcript_ptr + DIGEST_LEN * n_chunks  # advance transcript pointer

    poseidon8_compress(fs, transcript_ptr, new_fs)
    for i in unroll(1, n_chunks):
        poseidon8_compress(
            new_fs + ((i - 1) * DIGEST_LEN),
            transcript_ptr + i * DIGEST_LEN,
            new_fs + i * DIGEST_LEN,
        )
    return new_fs + DIGEST_LEN * (n_chunks - 1), transcript_ptr


@inline
def fs_receive_ef_inlined(fs, n):
    new_fs, ef_ptr = fs_receive_chunks(fs, div_ceil(n * DIM, DIGEST_LEN))
    for i in unroll(n * DIM, next_multiple_of(n * DIM, DIGEST_LEN)):
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
    new_fs, ef_ptr = fs_receive_chunks(fs, div_ceil(n * DIM, DIGEST_LEN))
    for i in unroll(n * DIM, next_multiple_of(n * DIM, DIGEST_LEN)):
        assert ef_ptr[i] == 0
    return new_fs, ef_ptr


def fs_print_state(fs_state):
    for i in unroll(0, FS_SIZE):
        print(i, fs_state[i])
    return


def fs_sample_data_with_offset(fs, n_chunks: Const, offset):
    # Like fs_sample_chunks but uses domain separators [offset..offset+n_chunks-1].
    # Only returns the sampled data, does NOT update fs.
    sampled = Array(n_chunks * DIGEST_LEN)
    for i in unroll(0, n_chunks):
        domain_sep = Array(DIGEST_LEN)
        domain_sep[0] = offset + i
        zero_digest_tail(domain_sep + 1)
        poseidon8_compress(domain_sep, fs, sampled + i * DIGEST_LEN)
    return sampled


def fs_finalize_sample(fs, total_n_chunks):
    # Compute new fs state using domain_sep = total_n_chunks
    # (same as the last poseidon call in fs_sample_chunks).
    new_fs = Array(FS_SIZE)
    domain_sep = Array(DIGEST_LEN)
    domain_sep[0] = total_n_chunks
    zero_digest_tail(domain_sep + 1)
    poseidon8_compress(domain_sep, fs, new_fs)
    new_fs[FS_TPTR] = fs[FS_TPTR]  # same transcript pointer
    return new_fs


@inline
def fs_sample_queries(fs, n_samples):
    debug_assert(n_samples < 512)
    # total_chunks = ceil(n_samples / DIGEST_LEN). With DIGEST_LEN=4 we shift
    # right by 2 and check whether the low 2 bits are nonzero. BE decomposition:
    # nb[0] = bit 8 (MSB), nb[8] = bit 0 (LSB).
    nb = checked_decompose_bits_small_value_const(n_samples, 9)
    floor_div = nb[0] * 64 + nb[1] * 32 + nb[2] * 16 + nb[3] * 8 + nb[4] * 4 + nb[5] * 2 + nb[6]
    has_remainder = 1 - (1 - nb[7]) * (1 - nb[8])
    total_chunks = floor_div + has_remainder
    # Sample exactly the needed chunks (dispatch via match_range to keep n_chunks const)
    sampled = match_range(total_chunks, range(0, 129), lambda nc: fs_sample_data_with_offset(fs, nc, 0))
    new_fs = fs_finalize_sample(fs, total_chunks)
    return sampled, new_fs
