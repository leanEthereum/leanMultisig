from snark_lib import *

TWO_ADDICITY = 24
ROOT_24 = 1791270792  # root of unity of order 2^24

LOG_M = 6

W = ROOT_24**(2**(TWO_ADDICITY - LOG_M - 1))  # root of unity of order 2*(M + 1)

M = 2**LOG_M
DIM = 5



def main():
    r = Array(DIM)
    r[0] = 11
    r[1] = 22
    r[2] = 565
    r[3] = 12
    r[4] = 989898

    arr1 = random_slice_fast(r)
    arr2 = random_slice_slow(r)
    for j in unroll(0, 2 * M):
        for d in unroll(0, DIM):
            assert arr1[j * DIM + d] == arr2[j * DIM + d]
    return

# Computes c_j(r) for j = 0, 1, ..., 2m-1
# $$
# c_j(r) \;=\; \sum_{k=m}^{2m-1} r^{k-m} \cdot \omega^{-jk},
# \qquad j = 0, 1, \ldots, 2m-1.
# $$
def random_slice_fast(r):
    # Closed form: alpha_j = r * w^{-j}, alpha_j^m = r^m * (-1)^j.
    # c_j = (-1)^j * (alpha_j^m - 1) / (alpha_j - 1)
    #     = ((rm - 1) if j even else (rm + 1)) / (alpha_j - 1)
    # with rm = r^m. All denominators are batch-inverted via Montgomery's trick.
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

# same as above, but naive O(m^2) implementation
def random_slice_slow(r):
    # arr[j] = sum_{i=0}^{m-1} r^i * w^{-j(i+m)}
    arr = Array(2 * M * DIM)

    # r_powers[i] = r^i for i in [0, M)
    r_powers = Array(M * DIM)
    r_powers[0] = 1
    for d in unroll(1, DIM):
        r_powers[d] = 0
    for i in unroll(1, M):
        dot_product_ee(r_powers + (i - 1) * DIM, r, r_powers + i * DIM)

    for j in unroll(0, 2 * M):
        # terms[i] = w^{-j(i+m)} * r^i, fully unrolled as scalar*EF muls.
        terms = Array(M * DIM)
        for i in unroll(0, M):
            coef = W ** ((2 * M - (j * (i + M)) % (2 * M)) % (2 * M))
            for d in unroll(0, DIM):
                terms[i * DIM + d] = coef * r_powers[i * DIM + d]

        # partials[i] = terms[0] + ... + terms[i] via length-1 add_ee.
        partials = Array(M * DIM)
        for d in unroll(0, DIM):
            partials[d] = terms[d]
        for i in unroll(1, M):
            add_ee(partials + (i - 1) * DIM, terms + i * DIM, partials + i * DIM)

        for d in unroll(0, DIM):
            arr[j * DIM + d] = partials[(M - 1) * DIM + d]

    return arr
