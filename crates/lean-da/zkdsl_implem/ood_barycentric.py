from snark_lib import *

# Extension-only barycentric low-degree check for a natural-order length-2M
# row codeword. This is the upstream evens/odds barycentric identity, but with
# base-domain constants embedded as extension elements and with strided reads
# from the natural-order row. Domain constants are passed as compile-time
# arguments to avoid colliding with the importing file's declarations.
#
#   sum_j s_L[j] * row[2j] = sum_j s_R[j] * row[2j + 1]
#
# where
#   s_L[j] = (r^M - 1) / (r * u^{-j} - 1)
#   s_R[j] = -(r^M + 1) / (r * w^{-1} * u^{-j} - 1)

OOD_BARY_DIM = 5


def base_const_ext(value: Const):
    ptr = Array(OOD_BARY_DIM)
    ptr[0] = value
    for d in unroll(1, OOD_BARY_DIM):
        ptr[d] = 0
    return ptr


def barycentric_slices_ext(
    r,
    m: Const,
    log_m: Const,
    u_inv_value: Const,
    w_inv_value: Const,
):
    slices = Array(2 * m * OOD_BARY_DIM)
    slice_L = slices
    slice_R = slices + m * OOD_BARY_DIM

    r_pow_log = Array((log_m + 1) * OOD_BARY_DIM)
    for d in unroll(0, OOD_BARY_DIM):
        r_pow_log[d] = r[d]
    for k in unroll(1, log_m + 1):
        dot_product_ee(
            r_pow_log + (k - 1) * OOD_BARY_DIM,
            r_pow_log + (k - 1) * OOD_BARY_DIM,
            r_pow_log + k * OOD_BARY_DIM,
        )
    rm = r_pow_log + log_m * OOD_BARY_DIM

    const_L = Array(OOD_BARY_DIM)
    const_L[0] = rm[0] - 1
    for d in unroll(1, OOD_BARY_DIM):
        const_L[d] = rm[d]

    const_R = Array(OOD_BARY_DIM)
    const_R[0] = (0 - rm[0]) - 1
    for d in unroll(1, OOD_BARY_DIM):
        const_R[d] = 0 - rm[d]

    u_inv = base_const_ext(u_inv_value)
    w_inv = base_const_ext(w_inv_value)
    s_L = Array(m * OOD_BARY_DIM)
    s_R = Array(m * OOD_BARY_DIM)
    for d in unroll(0, OOD_BARY_DIM):
        s_L[d] = r[d]
    dot_product_ee(w_inv, r, s_R)
    for j in unroll(1, m):
        dot_product_ee(
            u_inv,
            s_L + (j - 1) * OOD_BARY_DIM,
            s_L + j * OOD_BARY_DIM,
        )
        dot_product_ee(
            u_inv,
            s_R + (j - 1) * OOD_BARY_DIM,
            s_R + j * OOD_BARY_DIM,
        )

    dens_L = Array(m * OOD_BARY_DIM)
    dens_R = Array(m * OOD_BARY_DIM)
    for j in unroll(0, m):
        dens_L[j * OOD_BARY_DIM] = s_L[j * OOD_BARY_DIM] - 1
        dens_R[j * OOD_BARY_DIM] = s_R[j * OOD_BARY_DIM] - 1
        for d in unroll(1, OOD_BARY_DIM):
            dens_L[j * OOD_BARY_DIM + d] = s_L[j * OOD_BARY_DIM + d]
            dens_R[j * OOD_BARY_DIM + d] = s_R[j * OOD_BARY_DIM + d]

    for j in unroll(0, m):
        dot_product_ee(
            dens_L + j * OOD_BARY_DIM,
            slice_L + j * OOD_BARY_DIM,
            const_L,
        )
        dot_product_ee(
            dens_R + j * OOD_BARY_DIM,
            slice_R + j * OOD_BARY_DIM,
            const_R,
        )

    return slice_L, slice_R


def barycentric_check_natural_order(
    row,
    r,
    m: Const,
    log_m: Const,
    u_inv_value: Const,
    w_inv_value: Const,
):
    slice_L, slice_R = barycentric_slices_ext(r, m, log_m, u_inv_value, w_inv_value)
    eval_check = Array(OOD_BARY_DIM)
    dot_product_ee_strided_a(row, slice_L, eval_check, m, 2 * OOD_BARY_DIM)
    dot_product_ee_strided_a(
        row + OOD_BARY_DIM,
        slice_R,
        eval_check,
        m,
        2 * OOD_BARY_DIM,
    )
    return
