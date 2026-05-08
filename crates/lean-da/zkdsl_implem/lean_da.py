from snark_lib import *

TWO_ADDICITY = 24
ROOT_24 = 1791270792  # root of unity of order 2^24

LOG_M = LOG_M_PLACEHOLDER

W = ROOT_24**(2**(TWO_ADDICITY - LOG_M - 1))  # root of unity of order 2*(M + 1)

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
    for i in range(0, DIGEST_LEN):
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
# with rm = r^m. All denominators are batch-inverted via Montgomery's trick.
def rs_parity_coeffs(r):
    arr = Array(2 * M * DIM)

    # rm = r^m via LOG_M repeated squarings of r.
    r_pow_log = Array((LOG_M + 1) * DIM)  # r^(2^0), r^(2^1), ..., r^(2^LOG_M) = r^M
    for d in unroll(0, DIM):
        r_pow_log[d] = r[d]
    for k in unroll(1, LOG_M + 1):
        dot_product_ee(r_pow_log + (k - 1) * DIM, r_pow_log + (k - 1) * DIM, r_pow_log + k * DIM)
    rm = r_pow_log + LOG_M * DIM

    # alphas[j] = r * w^{-j} (scalar*EF, so element-wise base muls).
    # dens[j]   = alpha_j - 1.
    alphas = Array(2 * M * DIM)
    dens = Array(2 * M * DIM)
    for d in unroll(0, DIM):
        alphas[d] = r[d]
    dens[0] = r[0] - 1
    for d in unroll(1, DIM):
        dens[d] = r[d]
    for j in unroll(1, 2 * M):
        coef = W ** ((2 * M - j) % (2 * M))
        for d in unroll(0, DIM):
            alphas[j * DIM + d] = coef * r[d]
        dens[j * DIM] = alphas[j * DIM] - 1
        for d in unroll(1, DIM):
            dens[j * DIM + d] = alphas[j * DIM + d]

    # Forward pass: forward[j] = den[0] * den[1] * ... * den[j].
    forward = Array(2 * M * DIM)
    for d in unroll(0, DIM):
        forward[d] = dens[d]
    for j in unroll(1, 2 * M):
        dot_product_ee(forward + (j - 1) * DIM, dens + j * DIM, forward + j * DIM)

    # qs[2M-1] is the only true inversion: forward[2M-1] * qs[2M-1] = 1.
    one_ef = Array(DIM)
    one_ef[0] = 1
    for d in unroll(1, DIM):
        one_ef[d] = 0

    qs = Array(2 * M * DIM)
    dot_product_ee(forward + (2 * M - 1) * DIM, qs + (2 * M - 1) * DIM, one_ef)

    # Backward pass:
    #   invs[idx] = qs[idx] * forward[idx-1]   (= 1 / dens[idx])
    #   qs[idx-1] = qs[idx] * dens[idx]        (= 1 / forward[idx-1])
    invs = Array(2 * M * DIM)
    for k in unroll(0, 2 * M - 1):
        idx = 2 * M - 1 - k  # idx walks from 2M-1 down to 1
        dot_product_ee(qs + idx * DIM, forward + (idx - 1) * DIM, invs + idx * DIM)
        dot_product_ee(qs + idx * DIM, dens + idx * DIM, qs + (idx - 1) * DIM)
    for d in unroll(0, DIM):
        invs[d] = qs[d]

    # Numerators after sign collapse: only two distinct values.
    rm_minus_1 = Array(DIM)
    rm_minus_1[0] = rm[0] - 1
    for d in unroll(1, DIM):
        rm_minus_1[d] = rm[d]
    rm_plus_1 = Array(DIM)
    rm_plus_1[0] = rm[0] + 1
    for d in unroll(1, DIM):
        rm_plus_1[d] = rm[d]

    for j in unroll(0, M):
        dot_product_ee(rm_minus_1, invs + (2 * j) * DIM, arr + (2 * j) * DIM)
        dot_product_ee(rm_plus_1, invs + (2 * j + 1) * DIM, arr + (2 * j + 1) * DIM)

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
