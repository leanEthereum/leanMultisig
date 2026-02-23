from snark_lib import *
from hashing import *

F_BITS = 31  # koala-bear = 31 bits

TWO_ADICITY = 24
ROOT = 1791270792  # of order 2^TWO_ADICITY

def div_ceil_dynamic(a, b: Const):
    debug_assert(a <= 150)
    res = match_range(a, range(0, 151), lambda i: div_ceil(i, b))
    return res


@inline
def powers(alpha, n):
    # alpha: EF
    # n: F
    assert n < 512
    assert 0 < n
    res = match_range(n, range(1, 512), lambda i: powers_const(alpha, i))
    return res


def powers_const(alpha, n: Const):
    # alpha: EF
    # n: F

    res = Array(n * DIM)
    set_to_one(res)
    for i in unroll(0, n - 1):
        mul_extension(res + i * DIM, alpha, res + (i + 1) * DIM)
    return res


@inline
def unit_root_pow_dynamic(domain_size, index_bits):
    # index_bits is a pointer to domain_size bits
    debug_assert(domain_size < 26)
    debug_assert(0 < domain_size)
    res = match_range(domain_size, range(1, 26), lambda i: unit_root_pow_const(i, index_bits))
    return res


def unit_root_pow_const(domain_size: Const, index_bits):
    prod: Mut = (index_bits[0] * ROOT ** (2 ** (TWO_ADICITY - domain_size))) + (1 - index_bits[0])
    for i in unroll(1, domain_size):
        prod *= (index_bits[i] * ROOT ** (2 ** (TWO_ADICITY - domain_size + i))) + (1 - index_bits[i])
    return prod


def poly_eq_extension_dynamic(point, n):
    debug_assert(n < 9)
    res = match_range(n, range(0, 1), lambda i: ONE_VEC_PTR, range(1, 9), lambda i: poly_eq_extension(point, i))
    return res


def poly_eq_extension(point, n: Const):
    # Example: for n = 2: eq(x, y) = [(1 - x)(1 - y), (1 - x)y, x(1 - y), xy]

    res = Array((2 ** (n + 1) - 1) * DIM)
    set_to_one(res)

    for s in unroll(0, n):
        p = point + (n - 1 - s) * DIM
        for i in unroll(0, 2**s):
            mul_extension(p, res + (2**s - 1 + i) * DIM, res + (2 ** (s + 1) - 1 + 2**s + i) * DIM)
            sub_extension(
                res + (2**s - 1 + i) * DIM,
                res + (2 ** (s + 1) - 1 + 2**s + i) * DIM,
                res + (2 ** (s + 1) - 1 + i) * DIM,
            )
    return res + (2**n - 1) * DIM

def eq_mle_extension(a, b, n):
    debug_assert(n < 30)
    debug_assert(0 < n)
    res = Array(DIM)
    match_range(n, range(1, 30), lambda i: poly_eq_ee(a, b, res, i))
    return res


@inline
def eq_mle_base_extension(a, b, n):
    debug_assert(n <= 30)
    debug_assert(0 < n)
    res = Array(DIM)
    match_range(n, range(1, 31), lambda i: poly_eq_be(a, b, res, i))
    return res


def eq_mle_extension_base_const(a, b, n: Const):
    # a: base (n elements, stride 1)
    # b: extension (n elements, stride DIM)
    # poly_eq_be with length n computes prod_i poly_eq(a[i], b[i]) via multiplicative accumulation
    res = Array(DIM)
    poly_eq_be(a, b, res, n)
    return res

@inline
def expand_from_univariate_base(alpha, n):
    debug_assert(n < 23)
    debug_assert(0 < n)
    res = match_range(n, range(1, 23), lambda i: expand_from_univariate_base_const(alpha, i))
    return res


def expand_from_univariate_base_const(alpha, n: Const):
    # "expand_from_univariate"
    # alpha: F

    res = Array(n)
    current: Mut = alpha
    for i in unroll(0, n):
        res[i] = current
        current *= current
    return res


def expand_from_univariate_ext(alpha, n):
    res = Array(n * DIM)
    copy_5(alpha, res)
    for i in range(0, n - 1):
        mul_extension(res + i * DIM, res + i * DIM, res + (i + 1) * DIM)
    return res


def univariate_eval_on_base(coeffs, alpha, n: Const):
    # coeffs= univariate poly of degree 2^n
    # alpha: base field element
    # -> evaluates it at (1, alpha, alpha^2, alpha^4, ..., alpha^(2^(n-1)))
    alpha_powers = Array(2**n)
    alpha_powers[0] = 1
    for i in unroll(0, 2**n - 1):
        alpha_powers[i + 1] = alpha_powers[i] * alpha
    result = Array(DIM)
    dot_product_be(alpha_powers, coeffs, result, 2**n)
    return result


def eval_multilinear_coeffs_rev(coeffs, point, n: Const):
    # Evaluate multilinear polynomial in coefficient form (bit-reversed) at point.
    basis = Array(2**n * DIM)
    set_to_one(basis)
    for k in unroll(0, n):
        for j in unroll(0, 2**k):
            mul_extension(basis + j * DIM, point + k * DIM, basis + (j + 2**k) * DIM)
    result = Array(DIM)
    dot_product_ee(coeffs, basis, result, 2**n)
    return result


def dot_product_be_dynamic(a, b, res, n):
    debug_assert(n <= 256)
    match_range(n, range(1, 257), lambda i: dot_product_be(a, b, res, i))
    return


def dot_product_be_const(a, b, res, n: Const):
    dot_product_be(a, b, res, n)
    return


def dot_product_ee_dynamic(a, b, res, n):
    debug_assert(n <= 256)
    match_range(n, range(1, 257), lambda i: dot_product_ee(a, b, res, i))
    return


def dot_product_ee_const(a, b, res, n: Const):
    dot_product_ee(a, b, res, n)
    return


def mle_of_01234567_etc(point, n):
    if n == 0:
        return ZERO_VEC_PTR
    else:
        e = mle_of_01234567_etc(point + DIM, n - 1)
        a = one_minus_self_extension_ret(point)
        b = mul_extension_ret(a, e)
        power_of_2 = powers_of_two(n - 1)
        c = add_base_extension_ret(power_of_2, e)
        d = mul_extension_ret(point, c)
        res = add_extension_ret(b, d)
        return res


def range_check_power_of_2(a, n_bits: Const):
    # assert a < 2**n_bits
    debug_assert(n_bits < 30)
    if n_bits <= 16:
        assert a < 2**n_bits
    else:
        lo: Imu
        hi: Imu
        hint_decompose_16(a, lo, hi)
        assert lo < 2**16
        assert hi < 2**(n_bits - 16)
        assert a == lo + hi * 2**16
    return


@inline
def checked_less_than(a, b):
    res: Imu
    hint_less_than(a, b, res)
    assert res * (1 - res) == 0
    if res == 1:
        assert a < b
    else:
        assert b <= a
    return res


@inline
def maximum(a, b):
    is_a_less_than_b = checked_less_than(a, b)
    res: Imu
    if is_a_less_than_b == 1:
        res = b
    else:
        res = a
    return res


@inline
def powers_of_two(n):
    debug_assert(n < 32)
    res = match_range(n, range(0, 32), lambda i: 2**i)
    return res


@inline
def mul_extension_ret(a, b):
    res = Array(DIM)
    dot_product_ee(a, b, res)
    return res


@inline
def mul_extension(a, b, c):
    dot_product_ee(a, b, c)
    return


@inline
def add_extension_ret(a, b):
    c = Array(DIM)
    add_ee(a, b, c)
    return c


@inline
def add_extension(a, b, c):
    add_ee(a, b, c)
    return


@inline
def one_minus_self_extension_ret(a):
    res = Array(DIM)
    one_minus_self_extension(a, res)
    return res


@inline
def one_minus_self_extension(a, res):
    res[0] = 1 - a[0]
    for i in unroll(1, DIM):
        res[i] = 0 - a[i]
    return


@inline
def opposite_extension_ret(a):
    res = Array(DIM)
    for i in unroll(0, DIM):
        res[i] = 0 - a[i]
    return res


@inline
def add_base_extension_ret(a, b):
    # a: base
    # b: extension
    res = Array(DIM)
    res[0] = a + b[0]
    for i in unroll(1, DIM):
        res[i] = b[i]
    return res


@inline
def mul_base_extension_ret(a, b):
    # a: base field value (not a pointer)
    # b: extension pointer
    a_ptr = Array(1)
    a_ptr[0] = a
    res = Array(DIM)
    dot_product_be(a_ptr, b, res)
    return res


@inline
def div_extension_ret(n, d):
    quotient = Array(DIM)
    dot_product_ee(d, quotient, n)
    return quotient


@inline
def sub_extension(a, b, c):
    for i in unroll(0, DIM):
        c[i] = a[i] - b[i]
    return


@inline
def sub_base_extension_ret(a, b):
    # a: base
    # b: extension
    # return a - b
    res = Array(DIM)
    res[0] = a - b[0]
    for i in unroll(1, DIM):
        res[i] = 0 - b[i]
    return res


@inline
def sub_extension_base_ret(a, b):
    # a: extension
    # b: base
    # return a - b
    res = Array(DIM)
    res[0] = a[0] - b
    for i in unroll(1, DIM):
        res[i] = a[i]
    return res


@inline
def sub_extension_ret(a, b):
    c = Array(DIM)
    for i in unroll(0, DIM):
        c[i] = a[i] - b[i]
    return c


@inline
def copy_5(a, b):
    dot_product_ee(a, ONE_VEC_PTR, b)
    return


@inline
def set_to_5_zeros(a):
    zero_ptr = ZERO_VEC_PTR
    dot_product_ee(a, ONE_VEC_PTR, zero_ptr)
    return


@inline
def set_to_7_zeros(a):
    zero_ptr = ZERO_VEC_PTR
    dot_product_ee(a, ONE_VEC_PTR, zero_ptr)
    a[5] = 0
    a[6] = 0
    return


@inline
def set_to_8_zeros(a):
    zero_ptr = ZERO_VEC_PTR
    dot_product_ee(a, ONE_VEC_PTR, zero_ptr)
    dot_product_ee(a + (8 - DIM), ONE_VEC_PTR, zero_ptr)
    return


@inline
def copy_8(a, b):
    dot_product_ee(a, ONE_VEC_PTR, b)
    dot_product_ee(a + (8 - DIM), ONE_VEC_PTR, b + (8 - DIM))
    return


@inline
def copy_16(a, b):
    dot_product_ee(a, ONE_VEC_PTR, b)
    dot_product_ee(a + 5, ONE_VEC_PTR, b + 5)
    dot_product_ee(a + 10, ONE_VEC_PTR, b + 10)
    a[15] = b[15]
    return


@inline
def copy_many_ef(a, b, n):
    for i in unroll(0, n):
        dot_product_ee(a + i * DIM, ONE_VEC_PTR, b + i * DIM)
    return


@inline
def set_to_one(a):
    dot_product_ee(ONE_VEC_PTR, ONE_VEC_PTR, a)
    return


def print_ef(a):
    for i in unroll(0, DIM):
        print(a[i])
    return


def print_vec(a):
    for i in unroll(0, DIGEST_LEN):
        print(a[i])
    return


@inline
def read_memory(ptr):
    mem = 0
    return mem[ptr]


@inline
def univariate_polynomial_eval(coeffs, point, degree):
    powers = powers_const(point, degree + 1)
    res = Array(DIM)
    dot_product_ee(coeffs, powers, res, degree + 1)
    return res


@inline
def sum_2_ef_fractions(a_num, a_den, b_num, b_den):
    common_den = mul_extension_ret(a_den, b_den)
    a_num_mul_b_den = mul_extension_ret(a_num, b_den)
    b_num_mul_a_den = mul_extension_ret(b_num, a_den)
    sum_num = add_extension_ret(a_num_mul_b_den, b_num_mul_a_den)
    return sum_num, common_den


# p = 2^31 - 2^24 + 1
# in binary: p = 1111111000000000000000000000001
#        p - 1 = 1111111000000000000000000000000
#        p - 2 = 1111110111111111111111111111111
#        p - 3 = 1111110111111111111111111111110
#        ...
# Any field element (< p) is either:
# -   1111111    | 00...00
# - not(1111111) | xx...xx
def checked_decompose_bits(a):
    # return a pointer to the 31 bits of a
    # .. and the first 24 partial sums of these bits
    bits = Array(F_BITS)
    hint_decompose_bits(a, bits, F_BITS, LITTLE_ENDIAN)

    for i in unroll(0, F_BITS):
        assert bits[i] * (1 - bits[i]) == 0
    partial_sums_24 = Array(24)
    partial_sums_24[0] = bits[0]
    for i in unroll(1, 24):
        partial_sums_24[i] = partial_sums_24[i - 1] + bits[i] * 2**i
    sum_7: Mut = bits[24]
    for i in unroll(1, 7):
        sum_7 += bits[24 + i] * 2**i
    if sum_7 == 127:
        assert partial_sums_24[23] == 0

    assert a == partial_sums_24[23] + sum_7 * 2**24
    return bits, partial_sums_24

def checked_decompose_bits_small_value_const(to_decompose, n_bits: Const):
    bits = Array(n_bits)
    hint_decompose_bits(to_decompose, bits, n_bits, BIG_ENDIAN)
    sum: Mut = bits[n_bits - 1]
    assert sum * (1 - sum) == 0
    for i in unroll(1, n_bits):
        b = bits[n_bits - 1 - i]
        assert b * (1 - b) == 0
        sum += b * 2**i
    assert to_decompose == sum
    return bits


@inline
def checked_decompose_bits_small_value(to_decompose, n_bits):
    debug_assert(n_bits < 30)
    debug_assert(0 < n_bits)
    return match_range(
        n_bits,
        range(0, 1),
        lambda _: 0,
        range(1, 30),
        lambda i: checked_decompose_bits_small_value_const(to_decompose, i),
    )


@inline
def dot_product_ee_ret(a, b, n):
    res = Array(DIM)
    dot_product_ee_dynamic(a, b, res, n)
    return res


@inline
def sum_continuous_ef(slice_ef, len):
    debug_assert(len <= NUM_REPEATED_ONES_IN_RESERVED_MEMORY)
    res = Array(DIM)
    dot_product_be_dynamic(REPEATED_ONES_PTR, slice_ef, res, len)
    return res


def mle_of_zeros_then_ones(point, n_zeros, n_vars):
    if n_vars == 0:
        res = Array(DIM)
        res[0] = 1 - n_zeros
        for i in unroll(1, DIM):
            res[i] = 0
        return res

    n_values = powers_of_two(n_vars)
    debug_assert(n_zeros <= n_values)

    if n_zeros == n_values:
        return ZERO_VEC_PTR

    bits, _ = checked_decompose_bits(n_zeros)

    res: Mut = Array(DIM)
    set_to_one(res)

    for i in range(0, n_vars):
        p = point + (n_vars - 1 - i) * DIM
        if bits[i] == 0:
            one_minus_p = one_minus_self_extension_ret(p)
            tmp = mul_extension_ret(one_minus_p, res)
            res = add_extension_ret(tmp, p)
        else:
            res = mul_extension_ret(p, res)
    return res


@inline
def embed_in_ef(f):
    res = Array(DIM)
    res[0] = f
    for i in unroll(1, DIM):
        res[i] = 0
    return res


def next_mle(x, y, n):
    # x and y are pointers to n elements of extension field

    # Build eq_prefix[0..n+1] where eq_prefix[i] = prod_{j<i} eq(x[j], y[j])
    # and eq(a,b) = a*b + (1-a)*(1-b)
    eq_prefix = Array((n + 1) * DIM)
    set_to_one(eq_prefix)
    for i in range(0, n):
        xi = x + i * DIM
        yi = y + i * DIM
        eq_i = Array(DIM)
        poly_eq_ee(xi, yi, eq_i)
        mul_extension(eq_prefix + i * DIM, eq_i, eq_prefix + (i + 1) * DIM)

    # Build low_suffix[0..n+1] where low_suffix[i] = prod_{j>=i} (x[j] * (1-y[j]))
    low_suffix = Array((n + 1) * DIM)
    set_to_one(low_suffix + n * DIM)
    for i in range(0, n):
        idx = n - 1 - i
        xi = x + idx * DIM
        yi = y + idx * DIM
        one_minus_y = one_minus_self_extension_ret(yi)
        x_one_minus_y = mul_extension_ret(xi, one_minus_y)
        mul_extension(low_suffix + (idx + 1) * DIM, x_one_minus_y, low_suffix + idx * DIM)

    # Compute sum = Σ_{arr=0..n} (eq_prefix[arr] * (1-x[arr]) * y[arr] * low_suffix[arr+1])
    sum: Mut = ZERO_VEC_PTR
    for arr in range(0, n):
        x_arr = x + arr * DIM
        y_arr = y + arr * DIM
        one_minus_x = one_minus_self_extension_ret(x_arr)
        carry = mul_extension_ret(one_minus_x, y_arr)
        eq_carry = mul_extension_ret(eq_prefix + arr * DIM, carry)
        term = mul_extension_ret(eq_carry, low_suffix + (arr + 1) * DIM)
        sum = add_extension_ret(sum, term)

    # Compute prod = product of all x[i] * product of all y[i]
    prod: Mut = Array(DIM)
    set_to_one(prod)
    for i in range(0, n):
        prod = mul_extension_ret(prod, x + i * DIM)
    for i in range(0, n):
        prod = mul_extension_ret(prod, y + i * DIM)

    result = add_extension_ret(sum, prod)
    return result


@inline
def dot_product_with_the_base_vectors(slice):
    # slice: pointer to DIM extension field elements
    # cf constants.rs: by convention, [10000] [01000] [00100] [00010] [00001] is hardcoded in memory, starting at ONE_VEC_PTR
    res = Array(DIM)
    dot_product_ee(slice, ONE_VEC_PTR, res, DIM)
    return res


def _verify_log2_small(n, partial_sums_24, log2: Const):
    # For log2 in [3, 23]: verify n has exactly log2 bits
    assert partial_sums_24[log2 - 1] == n
    assert partial_sums_24[log2 - 2] != n
    return


def _verify_log2_large(n, log2: Const):
    # For log2 in [24, 30]: verify 2^(log2-1) < n <= 2^log2
    # by checking that n - 2^(log2-1) - 1 fits in (log2-1) bits
    remainder = n - 2**(log2 - 1) - 1
    _unused = checked_decompose_bits_small_value_const(remainder, log2 - 1)
    return


def log2_ceil_runtime(n):
    # requires: 2 < n <= 2^30
    log2: Imu
    hint_log2_ceil(n, log2)
    assert log2 < 31
    if powers_of_two(log2) != n:
        _, partial_sums_24 = checked_decompose_bits(n)
        match_range(log2,
            range(2, 24),
            lambda i: _verify_log2_small(n, partial_sums_24, i),
            range(24, 31),
            lambda i: _verify_log2_large(n, i))
    return log2

