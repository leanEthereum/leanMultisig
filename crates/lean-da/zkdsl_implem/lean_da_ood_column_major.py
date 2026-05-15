from snark_lib import *
from ood_barycentric import *

# Natural-order OOD-row construction for leanDA, with column-major witness
# memory.
#
# Each blob witness is a length-2M Reed-Solomon codeword in natural evaluation
# order: C_i[j] = P_i(w^j).  The public input commits to each systematic prefix
# d_i = H(C_i[0..M)), then to D = H(d_0, ..., d_{n-1}).  Each row coordinate
# x_i is derived from D, d_i, and i.  The OOD challenge z is derived from D,
# and the OOD row is the hash-domain column evaluation
#   OOD[j] = sum_i L_i(z) * C_i[j], where L_i is over the points x_i.
#
# The canonical witness layout is:
#   all_codewords[j][i] = C_i[j]
# where `j` is the row-codeword evaluation index and `i` is the blob index.
# This makes OOD-row composition a contiguous extension-field dot product.  The
# per-blob systematic hash is recovered by gathering a strided row stream into
# contiguous scratch before feeding the existing Poseidon chain hash.

TWO_ADDICITY = 24
ROOT_24 = 1791270792  # root of unity of order 2^24

LOG_M = LOG_M_PLACEHOLDER
M = 2 ** LOG_M
DIM = 5

N_BLOBS = N_BLOBS_PLACEHOLDER

W = ROOT_24**(2**(TWO_ADDICITY - LOG_M - 1))  # primitive 2M-th root of unity
U = W * W
U_INV = U ** (M - 1)
W_INV = W ** (2 * M - 1)

DIGEST_LEN = 8
LOG_LEAF_LEN_EXT = 4
LEAF_LEN_EXT = 2 ** LOG_LEAF_LEN_EXT
LEAF_LEN = LEAF_LEN_EXT * DIM
LEAF_NUM_CHUNKS = LEAF_LEN / DIGEST_LEN
LOG_NUM_LEAVES = LOG_M + 1 - LOG_LEAF_LEN_EXT
NUM_LEAVES = 2 ** LOG_NUM_LEAVES
SYSTEMATIC_NUM_CHUNKS = M * DIM / DIGEST_LEN
SYSTEMATIC_HASH_GROUPS = SYSTEMATIC_NUM_CHUNKS / 5

PUB_DIGESTS = 0
PUB_D = PUB_DIGESTS + N_BLOBS * DIGEST_LEN
PUB_Z = PUB_D + DIGEST_LEN
PUB_ROW_COEFFS = PUB_Z + DIM
PUB_OOD_ROOT = PUB_ROW_COEFFS + N_BLOBS * DIM


def main():
    debug_assert(LEAF_LEN % DIGEST_LEN == 0)
    debug_assert((M * DIM) % DIGEST_LEN == 0)

    all_codewords = Array(N_BLOBS * 2 * M * DIM)
    row_digests = Array(N_BLOBS * DIGEST_LEN)
    hint_witness("codewords_column_major", all_codewords)
    for i in unroll(0, N_BLOBS):
        hash_systematic_part_column_major(all_codewords, i, row_digests + i * DIGEST_LEN)
        assert_eq_digest(row_digests + i * DIGEST_LEN, PUB_DIGESTS + i * DIGEST_LEN)

    D = Array(DIGEST_LEN)
    chain_digests(row_digests, N_BLOBS, D)
    assert_eq_digest(D, PUB_D)

    z_digest = Array(DIGEST_LEN)
    derive_z(D, z_digest)
    assert_eq_ext(z_digest, PUB_Z)
    verify_row_coeffs(D, row_digests, PUB_Z, PUB_ROW_COEFFS)

    ood_row = compute_ood_row_column_major(all_codewords, PUB_ROW_COEFFS)
    ood_root = merkle_root_from_data(ood_row)
    assert_eq_digest(ood_root, PUB_OOD_ROOT)

    r_digest = Array(DIGEST_LEN)
    derive_ood_barycentric_challenge(D, PUB_Z, ood_root, r_digest)
    barycentric_check_natural_order(ood_row, r_digest, M, LOG_M, U_INV, W_INV)

    return



def gather_systematic_part_column_major(data, row_idx, dest):
    # Five 8-FE hash chunks contain exactly eight 5-limb extension elements.
    # This avoids floor division/modulo in the zkDSL while preserving row-major
    # systematic hash order: C_i[0], C_i[1], ..., C_i[M-1].
    for g in unroll(0, SYSTEMATIC_HASH_GROUPS):
        eval_base = g * 8
        out = g * 5 * DIGEST_LEN

        dest[out + 0] = data[(eval_base + 0) * N_BLOBS * DIM + row_idx * DIM + (0)]
        dest[out + 1] = data[(eval_base + 0) * N_BLOBS * DIM + row_idx * DIM + (1)]
        dest[out + 2] = data[(eval_base + 0) * N_BLOBS * DIM + row_idx * DIM + (2)]
        dest[out + 3] = data[(eval_base + 0) * N_BLOBS * DIM + row_idx * DIM + (3)]
        dest[out + 4] = data[(eval_base + 0) * N_BLOBS * DIM + row_idx * DIM + (4)]
        dest[out + 5] = data[(eval_base + 1) * N_BLOBS * DIM + row_idx * DIM + (0)]
        dest[out + 6] = data[(eval_base + 1) * N_BLOBS * DIM + row_idx * DIM + (1)]
        dest[out + 7] = data[(eval_base + 1) * N_BLOBS * DIM + row_idx * DIM + (2)]

        dest[out + 8] = data[(eval_base + 1) * N_BLOBS * DIM + row_idx * DIM + (3)]
        dest[out + 9] = data[(eval_base + 1) * N_BLOBS * DIM + row_idx * DIM + (4)]
        dest[out + 10] = data[(eval_base + 2) * N_BLOBS * DIM + row_idx * DIM + (0)]
        dest[out + 11] = data[(eval_base + 2) * N_BLOBS * DIM + row_idx * DIM + (1)]
        dest[out + 12] = data[(eval_base + 2) * N_BLOBS * DIM + row_idx * DIM + (2)]
        dest[out + 13] = data[(eval_base + 2) * N_BLOBS * DIM + row_idx * DIM + (3)]
        dest[out + 14] = data[(eval_base + 2) * N_BLOBS * DIM + row_idx * DIM + (4)]
        dest[out + 15] = data[(eval_base + 3) * N_BLOBS * DIM + row_idx * DIM + (0)]

        dest[out + 16] = data[(eval_base + 3) * N_BLOBS * DIM + row_idx * DIM + (1)]
        dest[out + 17] = data[(eval_base + 3) * N_BLOBS * DIM + row_idx * DIM + (2)]
        dest[out + 18] = data[(eval_base + 3) * N_BLOBS * DIM + row_idx * DIM + (3)]
        dest[out + 19] = data[(eval_base + 3) * N_BLOBS * DIM + row_idx * DIM + (4)]
        dest[out + 20] = data[(eval_base + 4) * N_BLOBS * DIM + row_idx * DIM + (0)]
        dest[out + 21] = data[(eval_base + 4) * N_BLOBS * DIM + row_idx * DIM + (1)]
        dest[out + 22] = data[(eval_base + 4) * N_BLOBS * DIM + row_idx * DIM + (2)]
        dest[out + 23] = data[(eval_base + 4) * N_BLOBS * DIM + row_idx * DIM + (3)]

        dest[out + 24] = data[(eval_base + 4) * N_BLOBS * DIM + row_idx * DIM + (4)]
        dest[out + 25] = data[(eval_base + 5) * N_BLOBS * DIM + row_idx * DIM + (0)]
        dest[out + 26] = data[(eval_base + 5) * N_BLOBS * DIM + row_idx * DIM + (1)]
        dest[out + 27] = data[(eval_base + 5) * N_BLOBS * DIM + row_idx * DIM + (2)]
        dest[out + 28] = data[(eval_base + 5) * N_BLOBS * DIM + row_idx * DIM + (3)]
        dest[out + 29] = data[(eval_base + 5) * N_BLOBS * DIM + row_idx * DIM + (4)]
        dest[out + 30] = data[(eval_base + 6) * N_BLOBS * DIM + row_idx * DIM + (0)]
        dest[out + 31] = data[(eval_base + 6) * N_BLOBS * DIM + row_idx * DIM + (1)]

        dest[out + 32] = data[(eval_base + 6) * N_BLOBS * DIM + row_idx * DIM + (2)]
        dest[out + 33] = data[(eval_base + 6) * N_BLOBS * DIM + row_idx * DIM + (3)]
        dest[out + 34] = data[(eval_base + 6) * N_BLOBS * DIM + row_idx * DIM + (4)]
        dest[out + 35] = data[(eval_base + 7) * N_BLOBS * DIM + row_idx * DIM + (0)]
        dest[out + 36] = data[(eval_base + 7) * N_BLOBS * DIM + row_idx * DIM + (1)]
        dest[out + 37] = data[(eval_base + 7) * N_BLOBS * DIM + row_idx * DIM + (2)]
        dest[out + 38] = data[(eval_base + 7) * N_BLOBS * DIM + row_idx * DIM + (3)]
        dest[out + 39] = data[(eval_base + 7) * N_BLOBS * DIM + row_idx * DIM + (4)]
    return


def hash_systematic_part_column_major(data, row_idx, dest):
    systematic = Array(M * DIM)
    gather_systematic_part_column_major(data, row_idx, systematic)
    hash_systematic_part(systematic, dest)
    return


def assert_eq_digest(a, b):
    for i in unroll(0, DIGEST_LEN):
        assert a[i] == b[i]
    return


@inline
def assert_eq_ext(a, b):
    for i in unroll(0, DIM):
        assert a[i] == b[i]
    return


@inline
def copy_ext(src, dest):
    for i in unroll(0, DIM):
        dest[i] = src[i]
    return


@inline
def copy_digest(src, dest):
    for i in unroll(0, DIGEST_LEN):
        dest[i] = src[i]
    return


@inline
def zero_digest():
    zero = Array(DIGEST_LEN)
    for i in unroll(0, DIGEST_LEN):
        zero[i] = 0
    return zero


def hash_systematic_part(data, dest):
    states = Array((SYSTEMATIC_NUM_CHUNKS - 2) * DIGEST_LEN)
    poseidon16_compress(data, data + DIGEST_LEN, states)
    for j in unroll(1, SYSTEMATIC_NUM_CHUNKS - 2):
        poseidon16_compress(
            states + (j - 1) * DIGEST_LEN,
            data + (j + 1) * DIGEST_LEN,
            states + j * DIGEST_LEN,
        )
    poseidon16_compress(
        states + (SYSTEMATIC_NUM_CHUNKS - 3) * DIGEST_LEN,
        data + (SYSTEMATIC_NUM_CHUNKS - 1) * DIGEST_LEN,
        dest,
    )
    return


def chain_digests(digests, n_digests: Const, dest):
    state: Mut = zero_digest()
    for i in unroll(0, n_digests):
        new_state = Array(DIGEST_LEN)
        poseidon16_compress(state, digests + i * DIGEST_LEN, new_state)
        state = new_state
    copy_digest(state, dest)
    return


def domain_tag(tag: Const):
    tag_ptr = Array(DIGEST_LEN)
    tag_ptr[0] = tag
    for i in unroll(1, DIGEST_LEN):
        tag_ptr[i] = 0
    return tag_ptr


@inline
def derive_z(D, dest):
    tag_z = domain_tag(1)
    poseidon16_compress(D, tag_z, dest)
    return


def derive_ood_barycentric_challenge(D, z, ood_root, dest):
    tag_ood = domain_tag(2)
    state = Array(DIGEST_LEN)
    poseidon16_compress(D, tag_ood, state)

    z_digest = Array(DIGEST_LEN)
    for d in unroll(0, DIM):
        z_digest[d] = z[d]
    for d in unroll(DIM, DIGEST_LEN):
        z_digest[d] = 0

    state_2 = Array(DIGEST_LEN)
    poseidon16_compress(state, z_digest, state_2)
    poseidon16_compress(state_2, ood_root, dest)
    return


def compute_ood_row_column_major(codewords_base, row_coeffs):
    ood_row = Array(2 * M * DIM)
    for j in unroll(0, 2 * M):
        dot_product_ee(
            codewords_base + j * N_BLOBS * DIM,
            row_coeffs,
            ood_row + j * DIM,
            N_BLOBS,
        )
    return ood_row


def verify_row_coeffs(D, row_digests, z, row_coeffs):
    row_points = Array(N_BLOBS * DIM)
    derive_row_points(D, row_digests, row_points)

    for i in unroll(0, N_BLOBS):
        numerator: Mut = one_ext()
        denominator: Mut = one_ext()
        for k in unroll(0, N_BLOBS):
            if k != i:
                z_minus_x = Array(DIM)
                sub_ext(z, row_points + k * DIM, z_minus_x)
                new_numerator = Array(DIM)
                dot_product_ee(numerator, z_minus_x, new_numerator)
                numerator = new_numerator

                x_i_minus_x_k = Array(DIM)
                sub_ext(row_points + i * DIM, row_points + k * DIM, x_i_minus_x_k)
                new_denominator = Array(DIM)
                dot_product_ee(denominator, x_i_minus_x_k, new_denominator)
                denominator = new_denominator

        lhs = Array(DIM)
        dot_product_ee(denominator, row_coeffs + i * DIM, lhs)
        assert_eq_ext(lhs, numerator)
    return


def derive_row_points(D, row_digests, row_points):
    for i in unroll(0, N_BLOBS):
        derive_row_point(D, row_digests + i * DIGEST_LEN, i, row_points + i * DIM)
    return


def derive_row_point(D, row_digest, row_idx: Const, dest):
    tag_row_x = domain_tag(3)
    state = Array(DIGEST_LEN)
    poseidon16_compress(D, tag_row_x, state)

    state_2 = Array(DIGEST_LEN)
    poseidon16_compress(state, row_digest, state_2)

    tag_idx = domain_tag(1000 + row_idx)
    point_digest = Array(DIGEST_LEN)
    poseidon16_compress(state_2, tag_idx, point_digest)

    for d in unroll(0, DIM):
        dest[d] = point_digest[d]
    return


@inline
def one_ext():
    one = Array(DIM)
    one[0] = 1
    for d in unroll(1, DIM):
        one[d] = 0
    return one


@inline
def sub_ext(a, b, dest):
    for d in unroll(0, DIM):
        dest[d] = a[d] - b[d]
    return


def hash_leaf(leaf, dest):
    states = Array((LEAF_NUM_CHUNKS - 2) * DIGEST_LEN)
    poseidon16_compress(leaf, leaf + DIGEST_LEN, states)
    for j in unroll(1, LEAF_NUM_CHUNKS - 2):
        poseidon16_compress(
            states + (j - 1) * DIGEST_LEN,
            leaf + (j + 1) * DIGEST_LEN,
            states + j * DIGEST_LEN,
        )
    poseidon16_compress(
        states + (LEAF_NUM_CHUNKS - 3) * DIGEST_LEN,
        leaf + (LEAF_NUM_CHUNKS - 1) * DIGEST_LEN,
        dest,
    )
    return


def merkle_root_from_data(data):
    leaves = Array(NUM_LEAVES * DIGEST_LEN)
    for i in unroll(0, NUM_LEAVES):
        hash_leaf(data + i * LEAF_LEN, leaves + i * DIGEST_LEN)

    layer: Mut = leaves
    for k in unroll(1, LOG_NUM_LEAVES + 1):
        layer_size = 2 ** (LOG_NUM_LEAVES - k)
        new_layer = Array(layer_size * DIGEST_LEN)
        for i in unroll(0, layer_size):
            poseidon16_compress(
                layer + (2 * i) * DIGEST_LEN,
                layer + (2 * i + 1) * DIGEST_LEN,
                new_layer + i * DIGEST_LEN,
            )
        layer = new_layer

    return layer
