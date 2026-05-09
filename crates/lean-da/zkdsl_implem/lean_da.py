from snark_lib import *

TWO_ADDICITY = 24
ROOT_24 = 1791270792  # root of unity of order 2^24

LOG_M = LOG_M_PLACEHOLDER

W = ROOT_24**(2**(TWO_ADDICITY - LOG_M - 1))  # root of unity of order 2*M

M = 2**LOG_M
DIM = 5

DIGEST_LEN = 8
LOG_LEAF_LEN = 8  # leaf size = 2^LOG_LEAF_LEN = 256 field elements
LEAF_LEN = 2 ** LOG_LEAF_LEN
LEAF_NUM_CHUNKS = div_floor(LEAF_LEN, DIGEST_LEN)  # = 32; chunks of 8 FE absorbed by the sponge
LOG_NUM_LEAVES = LOG_M + 1 - LOG_LEAF_LEN  # log2(2*M / LEAF_LEN)
NUM_LEAVES = 2 ** LOG_NUM_LEAVES

N_BLOBS = N_BLOBS_PLACEHOLDER  # number of codewords committed at once



def main():
    zero_vec_ptr = Array(DIGEST_LEN)
    for i in unroll(0, DIGEST_LEN):
        zero_vec_ptr[i] = 0

    codewords = Array(N_BLOBS * 2 * M)
    hint_witness("codewords", codewords)

    roots = Array(N_BLOBS)
    for i in unroll(0, N_BLOBS):
        roots[i] = merkle_root(codewords + i * 2 * M)
    
    # hash the merkle roots:
    state: Mut = zero_vec_ptr
    for i in unroll(0, N_BLOBS):
        new_state = Array(DIGEST_LEN)
        poseidon16_compress(state, roots + i * DIGEST_LEN, new_state)
        state = new_state
    
    # r is interpreted a random extension field element (<=> 5 base field elements)
    r = state # fiat-shamir: randomness is obtained by hashing all the previous merkle roots

    parity_slice = rs_parity_coeffs(r)

    for i in unroll(0, N_BLOBS):
        dot_product_be(codewords + i * 2 * M, parity_slice, zero_vec_ptr, 2 * M)

    return


# Computes c_j(r) for j = 0, 1, ..., 2m-1
# $$
# c_j(r) \;=\; \sum_{k=m}^{2m-1} r^{k-m} \cdot \omega^{-jk},
# \qquad j = 0, 1, \ldots, 2m-1.
# $$
# Closed form: alpha_j = r * w^{-j}, alpha_j^m = r^m * (-1)^j.
# c_j = (-1)^j * (alpha_j^m - 1) / (alpha_j - 1)
#     = ((rm - 1) if j even else (rm + 1)) / (alpha_j - 1)
# with rm = r^m.
#
# Each c_j is recovered via a single constraint dens_j * c_j = u_j (length-1
# dot_product_ee), which the prover satisfies by hinting c_j = u_j / dens_j.
# This avoids Montgomery's batch inversion entirely (the prover does the actual
# inversions outside the circuit, the VM just checks one ext-mul per coefficient).
def rs_parity_coeffs(r):
    arr = Array(2 * M * DIM)

    # rm = r^m via LOG_M repeated squarings of r.
    r_pow_log = Array((LOG_M + 1) * DIM)  # r^(2^0), r^(2^1), ..., r^(2^LOG_M) = r^M
    for d in unroll(0, DIM):
        r_pow_log[d] = r[d]
    for k in unroll(1, LOG_M + 1):
        dot_product_ee(r_pow_log + (k - 1) * DIM, r_pow_log + (k - 1) * DIM, r_pow_log + k * DIM)
    rm = r_pow_log + LOG_M * DIM

    # Numerators after sign collapse: u_j = (rm - 1) if j even else (rm + 1).
    rm_minus_1 = Array(DIM)
    rm_minus_1[0] = rm[0] - 1
    for d in unroll(1, DIM):
        rm_minus_1[d] = rm[d]
    rm_plus_1 = Array(DIM)
    rm_plus_1[0] = rm[0] + 1
    for d in unroll(1, DIM):
        rm_plus_1[d] = rm[d]

    # neg_one_ef = (-1) as an extension element.
    neg_one_ef = Array(DIM)
    neg_one_ef[0] = 0 - 1
    for d in unroll(1, DIM):
        neg_one_ef[d] = 0

    # alphas[j] = r * w^{-j} via a multiplicative recurrence:
    #   alphas[0] = r,  alphas[j] = alphas[j-1] * w_inv  (single length-1 base*ext call).
    # This avoids 2*M compile-time-constant writes for the per-j w^{-j} coefficients.
    w_inv_ptr = Array(1)
    w_inv_ptr[0] = W ** (2 * M - 1)  # w^{-1} since w has order 2*M
    alphas = Array(2 * M * DIM)
    for d in unroll(0, DIM):
        alphas[d] = r[d]
    for j in unroll(1, 2 * M):
        dot_product_be(w_inv_ptr, alphas + (j - 1) * DIM, alphas + j * DIM)

    # dens[j] = alphas[j] - 1 via a single length-1 ext+ext precompile call.
    dens = Array(2 * M * DIM)
    for j in unroll(0, 2 * M):
        add_ee(alphas + j * DIM, neg_one_ef, dens + j * DIM)

    # arr[j] = u_j / dens[j] = c_j, satisfied via constraint dens[j] * arr[j] = u_j.
    # The prover hints arr[j]; the VM solves the unknown operand for length-1 Mul.
    for j in unroll(0, M):
        dot_product_ee(dens + (2 * j) * DIM, arr + (2 * j) * DIM, rm_minus_1)
        dot_product_ee(dens + (2 * j + 1) * DIM, arr + (2 * j + 1) * DIM, rm_plus_1)

    return arr

@inline
def hash_leaf(leaf, dest):
    # fixed length: no IV needed
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


def merkle_root(codeword):
    leaves = Array(NUM_LEAVES * DIGEST_LEN)
    for i in unroll(0, NUM_LEAVES):
        hash_leaf(codeword + i * LEAF_LEN, leaves + i * DIGEST_LEN)

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
