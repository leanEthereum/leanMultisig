from snark_lib import *
from barycentric import *

DIGEST_LEN = 8
LOG_LEAF_LEN_EXT = 4  # leaf size = 2^LOG_LEAF_LEN_EXT = 16 extension elements (= 64 base FE)
LEAF_LEN_EXT = 2 ** LOG_LEAF_LEN_EXT
LEAF_LEN = LEAF_LEN_EXT * DIM  # base field elements per leaf
LEAF_NUM_CHUNKS = LEAF_LEN / DIGEST_LEN  # chunks of 8 FE absorbed by the sponge
LOG_NUM_LEAVES = LOG_M + 1 - LOG_LEAF_LEN_EXT  # log2((2*M) / LEAF_LEN_EXT)
NUM_LEAVES = 2 ** LOG_NUM_LEAVES

N_BLOBS = N_BLOBS_PLACEHOLDER  # number of codewords committed at once


def main():
    debug_assert(LEAF_LEN % DIGEST_LEN == 0)

    zero_vec_ptr = Array(DIGEST_LEN)
    for i in unroll(0, DIGEST_LEN):
        zero_vec_ptr[i] = 0

    # Each blob is 2*M extension field elements (= 2*M*DIM base field elements).
    codewords = Array(N_BLOBS * 2 * M * DIM)
    hint_witness("codewords", codewords)

    roots = Array(N_BLOBS)
    for i in unroll(0, N_BLOBS):
        roots[i] = merkle_root(codewords + i * 2 * M * DIM)

    # hash the merkle roots:
    state: Mut = zero_vec_ptr
    for i in unroll(0, N_BLOBS):
        new_state = Array(DIGEST_LEN)
        poseidon16_compress(state, roots + i * DIGEST_LEN, new_state)
        state = new_state

    # r is interpreted a random extension field element (<=> 5 base field elements)
    r = state # fiat-shamir: randomness is obtained by hashing all the previous merkle roots

    slice_L, slice_R = barycentric_slices(r)

    for i in unroll(0, N_BLOBS):
        eval_check = Array(DIM)
        dot_product_ee(codewords + i * 2 * M * DIM,             slice_L, eval_check, M)
        dot_product_ee(codewords + i * 2 * M * DIM + M * DIM,   slice_R, eval_check, M)

    return


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
