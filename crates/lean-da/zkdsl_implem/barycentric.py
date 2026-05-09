from snark_lib import *

# Constants and helpers for the Reed-Solomon barycentric parity check.
#
# A codeword (a_0, ..., a_{2M-1}) is a valid RS codeword (i.e. evaluations of
# some deg-<M polynomial on the 2M-th roots of unity) iff the unique deg-<M
# polynomial L through {(u^j, a_{2j})} equals the unique deg-<M polynomial R
# through {(w*u^j, a_{2j+1})}, where w is a primitive 2M-th root of unity and
# u = w^2 is the primitive M-th root.
#
# Soundness: pick a random extension element r and check L(r) == R(r). The
# barycentric form gives:
#     M*L(r) = sum_j slice_L[j] * a_{2j}      slice_L[j] = (r^M - 1) / (r * u^{-j} - 1)
#     M*R(r) = sum_j slice_R[j] * a_{2j+1}    slice_R[j] = -(r^M + 1) / (r * w^{-1} * u^{-j} - 1)
# (the 1/M factor cancels and is dropped from both sides.)

TWO_ADDICITY = 24
ROOT_24 = 1791270792  # root of unity of order 2^24

LOG_M = LOG_M_PLACEHOLDER

W = ROOT_24**(2**(TWO_ADDICITY - LOG_M - 1))  # primitive 2M-th root of unity
U = W * W                                     # primitive M-th root of unity
U_INV = U ** (2 ** LOG_M - 1)                 # u^{-1}
W_INV = W ** (2 * 2 ** LOG_M - 1)             # w^{-1}

M = 2 ** LOG_M
DIM = 5


def barycentric_slices(r):
    # Returns (slice_L, slice_R), each of length M extension field elements,
    # backed by a single contiguous Array of length 2*M*DIM.
    slices = Array(2 * M * DIM)
    slice_L = slices
    slice_R = slices + M * DIM

    # ---- Step 1: r^M via LOG_M repeated squarings.
    r_pow_log = Array((LOG_M + 1) * DIM)  # r^(2^0), r^(2^1), ..., r^(2^LOG_M) = r^M
    for d in unroll(0, DIM):
        r_pow_log[d] = r[d]
    for k in unroll(1, LOG_M + 1):
        dot_product_ee(r_pow_log + (k - 1) * DIM,
                       r_pow_log + (k - 1) * DIM,
                       r_pow_log + k * DIM)
    rm = r_pow_log + LOG_M * DIM

    # ---- Step 2: const_L = r^M - 1, const_R = -(r^M + 1).
    const_L = Array(DIM)
    const_L[0] = rm[0] - 1
    for d in unroll(1, DIM):
        const_L[d] = rm[d]
    const_R = Array(DIM)
    const_R[0] = (0 - rm[0]) - 1
    for d in unroll(1, DIM):
        const_R[d] = 0 - rm[d]

    # ---- Step 3: s_L[j] = r * u^{-j}  and  s_R[j] = r * w^{-1} * u^{-j} = r * w^{-(2j+1)}
    # via independent multiplicative recurrences (single length-1 base*ext call each step).
    u_inv_ptr = Array(1)
    u_inv_ptr[0] = U_INV
    w_inv_ptr = Array(1)
    w_inv_ptr[0] = W_INV
    s_L = Array(M * DIM)
    s_R = Array(M * DIM)
    for d in unroll(0, DIM):
        s_L[d] = r[d]
    dot_product_be(w_inv_ptr, r, s_R)  # s_R[0] = r * w^{-1}
    for j in unroll(1, M):
        dot_product_be(u_inv_ptr, s_L + (j - 1) * DIM, s_L + j * DIM)
        dot_product_be(u_inv_ptr, s_R + (j - 1) * DIM, s_R + j * DIM)

    # ---- Step 4: dens_L[j] = s_L[j] - 1, dens_R[j] = s_R[j] - 1
    # via a length-1 base+ext add (one ext_op row each).
    neg_one_ptr = Array(1)
    neg_one_ptr[0] = 0 - 1
    dens_L = Array(M * DIM)
    dens_R = Array(M * DIM)
    for j in unroll(0, M):
        add_be(neg_one_ptr, s_L + j * DIM, dens_L + j * DIM)
        add_be(neg_one_ptr, s_R + j * DIM, dens_R + j * DIM)

    # ---- Step 5: enforce dens_L[j] * slice_L[j] = const_L (and similarly for R)
    # via length-1 ext*ext dot products. The prover hints slice_L[j] / slice_R[j]
    # to satisfy each constraint (no in-circuit inversion).
    for j in unroll(0, M):
        dot_product_ee(dens_L + j * DIM, slice_L + j * DIM, const_L)
        dot_product_ee(dens_R + j * DIM, slice_R + j * DIM, const_R)

    return slice_L, slice_R
