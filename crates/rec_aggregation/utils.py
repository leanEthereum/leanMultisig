from snark_lib import *
from hashing import *

F_BITS = 64  # Goldilocks (P = 2^64 - 2^32 + 1, values fit in u64)
HALF_BITS = 32  # Goldilocks splits cleanly at 32:32 for canonical-form checks.

TWO_ADICITY = 32
ROOT = 1753635133440165772  # = 0x185629dcda58878c, of order 2^TWO_ADICITY

EFFECTIVE_TWO_ADICITY = EFFECTIVE_TWO_ADICITY_PLACEHOLDER


@inline
def build_preamble_memory():
    zero_vec_w = ZERO_VEC_PTR
    for i in unroll(0, ZERO_VEC_LEN):
        zero_vec_w[i] = 0

    sds_w = SAMPLING_DOMAIN_SEPARATOR_PTR
    sds_w[0] = 1
    for i in unroll(1, DIGEST_LEN):
        sds_w[i] = 0

    one_ef_w = ONE_EF_PTR
    one_ef_w[0] = 1
    for i in unroll(1, DIM):
        one_ef_w[i] = 0

    repeated_ones_w = REPEATED_ONES_PTR
    for i in unroll(0, NUM_REPEATED_ONES):
        repeated_ones_w[i] = 1
    return


def div_ceil_dynamic(a, b: Const):
    debug_assert(a <= 150)
    res = match_range(a, range(0, 151), lambda i: div_ceil(i, b))
    return res


@inline
def powers(alpha, n):
    # alpha: EF
    # n: F
    assert n < 400
    assert 0 < n
    # 2**log2_ceil(i) is not really necessary but helps reduce byetcode size (traedoff cycles / bytecode size)
    res = match_range(n, range(1, 400), lambda i: powers_const(alpha, 2**log2_ceil(i)))
    return res


def powers_const(alpha, n: Const):
    # alpha: EF
    # n: F
    debug_assert(n != 0)

    res = Array(n * DIM)
    set_to_one(res)
    if n == 1:
        return res
    copy_ef(alpha, res + DIM)
    for i in unroll(1, n - 1):
        mul_extension(res + i * DIM, res + DIM, res + (i + 1) * DIM)
    return res


def compute_eq_mle_extension_dynamic(point, n):
    debug_assert(n < 9)
    res = match_range(n, range(0, 1), lambda _: ONE_EF_PTR, range(1, 9), lambda i: compute_eq_mle_extension(point, i))
    return res


def product_first_n(values, n):
    # values: pointer to n EFs
    # Returns ∏_{i=0}^{n-1} values[i]
    debug_assert(n < 33)
    res = match_range(n, range(0, 1), lambda _: ONE_EF_PTR, range(1, 33), lambda i: product_first_n_const(values, i))
    return res

@inline
def product_first_n_const(values, n):
    debug_assert(n != 0)
    debug_assert(n <= NUM_REPEATED_ONES)
    res = Array(DIM)
    poly_eq_be(REPEATED_ONES_PTR, values, res, n)
    return res


def compute_eq_mle_extension(point, n: Const):
    # Example: for n = 2: eq(x, y) = [(1 - x)(1 - y), (1 - x)y, x(1 - y), xy]

    res = Array((2 ** (n + 1) - 1) * DIM)
    set_to_one(res)

    for s in unroll(0, n):
        p = Array(DIM)
        copy_ef(point + (n - 1 - s) * DIM, p)
        for i in unroll(0, 2**s):
            mul_extension(p, res + (2**s - 1 + i) * DIM, res + (2 ** (s + 1) - 1 + 2**s + i) * DIM)
            sub_extension(
                res + (2**s - 1 + i) * DIM,
                res + (2 ** (s + 1) - 1 + 2**s + i) * DIM,
                res + (2 ** (s + 1) - 1 + i) * DIM,
            )
    return res + (2**n - 1) * DIM


@inline
def poly_eq_extension_dynamic_to(a, b, dst, n):
    debug_assert(n < 33)
    debug_assert(0 < n)
    match_range(n, range(1, 33), lambda i: poly_eq_ee(a, b, dst, i))
    return


def poly_eq_extension_dynamic_ret(a, b, n):
    res = Array(DIM)
    poly_eq_extension_dynamic_to(a, b, res, n)
    return res


@inline
def poly_eq_base_extension_to(a, b, dst, n):
    debug_assert(n < 33)
    debug_assert(0 < n)
    match_range(n, range(1, 33), lambda i: poly_eq_be(a, b, dst, i))
    return


@inline
def poly_eq_base_extension(a, b, n):
    res = Array(DIM)
    poly_eq_base_extension_to(a, b, res, n)
    return res


@inline
def expand_from_univariate_base(alpha, n):
    debug_assert(n < 33)
    debug_assert(0 < n)
    res = match_range(n, range(1, 33), lambda i: expand_from_univariate_base_const(alpha, i))
    return res


def expand_from_univariate_base_const(alpha, n: Const):
    # "expand_from_univariate"
    # alpha: F

    res = Array(n)
    res[0] = alpha
    for i in unroll(1, n):
        res[i] = res[i - 1] * res[i - 1]
    return res


def expand_from_univariate_ext(alpha, n):
    res = Array(n * DIM)
    copy_ef(alpha, res)
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
        p = Array(DIM)
        copy_ef(point + k * DIM, p)
        for j in unroll(0, 2**k):
            mul_extension(basis + j * DIM, p, basis + (j + 2**k) * DIM)
    result = Array(DIM)
    dot_product_ee(coeffs, basis, result, 2**n)
    return result


@inline
def dot_product_be_dynamic(a, b, res, n):
    debug_assert(n < 400)
    match_range(n, range(1, 400), lambda i: dot_product_be(a, b, res, i))
    return

def dot_product_ee_dynamic(a, b, res, n):
    debug_assert(n < 400)
    match_range(n, range(1, 400), lambda i: dot_product_ee(a, b, res, i))
    return

def mle_of_01234567_etc(point, n):
    if n == 0:
        return ZERO_VEC_PTR
    else:
        e = mle_of_01234567_etc(point + DIM, n - 1)
        a = one_minus_self_extension_ret(point)
        b = mul_extension_ret(a, e)
        power_of_2 = two_exp(n - 1)
        c = add_base_extension_ret(power_of_2, e)
        d = mul_extension_ret(point, c)
        res = add_extension_ret(b, d)
        return res


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
def two_exp(n):
    debug_assert(n < 33)
    res = match_range(n, range(0, 33), lambda i: 2**i)
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
def one_minus_self_extension_ret(a):
    res = Array(DIM)
    add_ee(a, res, ONE_EF_PTR)
    return res


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
    a_ptr = Array(1)
    a_ptr[0] = a
    add_be(a_ptr, b, res)
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
    div_extension(n, d, quotient)
    return quotient

@inline
def div_extension(n, d, res):
    dot_product_ee(d, res, n)
    return


@inline
def sub_extension(a, b, c):
    # c = a - b <=> a = c + b
    add_ee(b, c, a)
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
    b_ptr = Array(1)
    b_ptr[0] = b
    add_be(b_ptr, res, a)
    return res


@inline
def sub_extension_ret(a, b):
    c = Array(DIM)
    for i in unroll(0, DIM):
        c[i] = a[i] - b[i]
    return c


# Semantic copy / zero helpers. Sized to Goldilocks (DIM=3, DIGEST_LEN=4,
# MESSAGE_LEN=4). Each helper is a thin wrapper over `dot_product_ee(_, ONE_EF_PTR, _)`
# which copies DIM elements via the extension-op precompile.


@inline
def copy_ef(a, b):
    # Copy one extension-field element = DIM entries.
    dot_product_ee(a, ONE_EF_PTR, b)
    return


@inline
def zero_ef(a):
    # Zero one extension-field element = DIM entries.
    zero_ptr = ZERO_VEC_PTR
    dot_product_ee(a, ONE_EF_PTR, zero_ptr)
    return


@inline
def zero_digest_tail(a):
    # Zero DIGEST_LEN-1 entries — typically called on `ptr + 1` after writing a
    # domain-sep byte into slot 0 of a digest-sized buffer. Under Goldilocks
    # DIGEST_LEN-1 == DIM so one dot_product_ee suffices.
    zero_ptr = ZERO_VEC_PTR
    dot_product_ee(a, ONE_EF_PTR, zero_ptr)
    return


@inline
def zero_digest(a):
    # Zero one digest = DIGEST_LEN entries via two overlapping DIM clears.
    zero_ptr = ZERO_VEC_PTR
    dot_product_ee(a, ONE_EF_PTR, zero_ptr)
    dot_product_ee(a + (DIGEST_LEN - DIM), ONE_EF_PTR, zero_ptr)
    return


@inline
def copy_digest(a, b):
    # Copy one digest = DIGEST_LEN entries via two overlapping DIM copies.
    dot_product_ee(a, ONE_EF_PTR, b)
    dot_product_ee(a + (DIGEST_LEN - DIM), ONE_EF_PTR, b + (DIGEST_LEN - DIM))
    return


@inline
def copy_message(a, b):
    # Copy one message = MESSAGE_LEN entries. Under Goldilocks MESSAGE_LEN ==
    # DIGEST_LEN, so this is structurally identical to `copy_digest`.
    dot_product_ee(a, ONE_EF_PTR, b)
    dot_product_ee(a + (DIGEST_LEN - DIM), ONE_EF_PTR, b + (DIGEST_LEN - DIM))
    return


@inline
def copy_poseidon_input(a, b):
    # Copy a full Poseidon8 input block = 2 × DIGEST_LEN entries.
    copy_digest(a, b)
    copy_digest(a + DIGEST_LEN, b + DIGEST_LEN)
    return


@inline
def copy_many_ef(a, b, n):
    for i in unroll(0, n):
        dot_product_ee(a + i * DIM, ONE_EF_PTR, b + i * DIM)
    return


@inline
def set_to_one(a):
    dot_product_ee(ONE_EF_PTR, ONE_EF_PTR, a)
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


# Goldilocks: p = 2^64 - 2^32 + 1 = 0xFFFFFFFF_00000001
#   p - 1 = 0xFFFFFFFF_00000000
#   p - 2 = 0xFFFFFFFE_FFFFFFFF
#   ...
# Any field element (< p) is either:
#   - high 32 bits = 0xFFFFFFFF and low 32 bits = 0
#   - high 32 bits < 0xFFFFFFFF and low 32 bits arbitrary
def checked_decompose_bits(a):
    # Return a pointer to the F_BITS=64 little-endian bits of `a`, plus the
    # partial sums over the low HALF_BITS=32 bits. Enforces canonicality.
    bits = Array(F_BITS)
    hint_decompose_bits(a, bits, F_BITS, LITTLE_ENDIAN)

    for i in unroll(0, F_BITS):
        assert bits[i] * (1 - bits[i]) == 0
    partial_sums_low = Array(HALF_BITS)
    partial_sums_low[0] = bits[0]
    for i in unroll(1, HALF_BITS):
        partial_sums_low[i] = partial_sums_low[i - 1] + bits[i] * 2**i
    sum_high: Mut = bits[HALF_BITS]
    for i in unroll(1, F_BITS - HALF_BITS):
        sum_high += bits[HALF_BITS + i] * 2**i
    # If the high 32 bits are all set, the low 32 bits must be zero (only p-1).
    if sum_high == 2**(F_BITS - HALF_BITS) - 1:
        assert partial_sums_low[HALF_BITS - 1] == 0

    assert a == partial_sums_low[HALF_BITS - 1] + sum_high * 2**HALF_BITS
    return bits, partial_sums_low


@inline
def whir_4_merkle_step_and_pow(v, state_in, path_chunk, state_out, power_shift):
    whir_do_4_merkle_levels(v, state_in, path_chunk, state_out)
    return ROOT ** (power_shift * v)


@inline
def whir_3_merkle_step_and_pow(v, state_in, path_chunk, state_out, power_shift):
    whir_do_3_merkle_levels(v, state_in, path_chunk, state_out)
    return ROOT ** (power_shift * (v % 8))


@inline
def whir_2_merkle_step_and_pow(v, state_in, path_chunk, state_out, power_shift):
    whir_do_2_merkle_levels(v, state_in, path_chunk, state_out)
    return ROOT ** (power_shift * (v % 4))


@inline
def whir_1_merkle_step_and_pow(v, state_in, path_chunk, state_out, power_shift):
    whir_do_1_merkle_level(v, state_in, path_chunk, state_out)
    return ROOT ** (power_shift * (v % 2))


@inline
def decompose_and_verify_merkle_query(a, domain_size, prev_root, num_chunks):
    # Decompose the full 64-bit Goldilocks FE `a` into 16 × 4-bit nibbles so
    # that `a == partial_sum` holds for any valid field element (no top-bits
    # restriction). The first `n_nibbles = ceil(domain_size/4)` nibbles encode
    # the Merkle query index modulo 2^domain_size.
    NUM_NIBBLES = F_BITS / 4
    nibbles = Array(NUM_NIBBLES)
    hint_decompose_bits_merkle_whir(nibbles, a, NUM_NIBBLES, 4)

    for i in unroll(0, NUM_NIBBLES):
        assert nibbles[i] < 16

    partial_sum: Mut = nibbles[0]
    for i in unroll(1, NUM_NIBBLES):
        partial_sum += nibbles[i] * 16**i

    assert a == partial_sum

    leaf_data = Array(num_chunks * DIGEST_LEN)
    hint_witness("merkle_leaf", leaf_data)
    leaf_hash = slice_hash_rtl(leaf_data, num_chunks)

    merkle_path = Array(domain_size * DIGEST_LEN)
    hint_witness("merkle_path", merkle_path)

    n_nibbles = div_ceil(domain_size, 4)
    states = Array((n_nibbles - 1) * DIGEST_LEN)

    prod: Mut = 1

    # First nibble: leaf_hash -> states[0]
    nib_pow = match_range(
        nibbles[0],
        range(0, 16),
        lambda v: whir_4_merkle_step_and_pow(v, leaf_hash, merkle_path, states, 2 ** (TWO_ADICITY - domain_size)),
    )
    prod *= nib_pow

    # Middle nibbles: states[k-1] -> states[k]
    for k in unroll(1, n_nibbles - 1):
        nib_pow = match_range(
            nibbles[k],
            range(0, 16),
            lambda v: whir_4_merkle_step_and_pow(
                v,
                states + (k - 1) * DIGEST_LEN,
                merkle_path + 4 * k * DIGEST_LEN,
                states + k * DIGEST_LEN,
                2 ** (TWO_ADICITY - domain_size + 4 * k),
            ),
        )
        prod *= nib_pow

    # Last nibble: states[-1] -> prev_root
    last_k = n_nibbles - 1
    last_state_in = states + (last_k - 1) * DIGEST_LEN
    last_path = merkle_path + 4 * last_k * DIGEST_LEN
    last_power_shift = 2 ** (TWO_ADICITY - domain_size + 4 * last_k)
    if domain_size % 4 == 0:
        nib_pow = match_range(
            nibbles[last_k],
            range(0, 16),
            lambda v: whir_4_merkle_step_and_pow(v, last_state_in, last_path, prev_root, last_power_shift),
        )
        prod *= nib_pow
    elif domain_size % 4 == 1:
        nib_pow = match_range(
            nibbles[last_k],
            range(0, 16),
            lambda v: whir_1_merkle_step_and_pow(v, last_state_in, last_path, prev_root, last_power_shift),
        )
        prod *= nib_pow
    elif domain_size % 4 == 2:
        nib_pow = match_range(
            nibbles[last_k],
            range(0, 16),
            lambda v: whir_2_merkle_step_and_pow(v, last_state_in, last_path, prev_root, last_power_shift),
        )
        prod *= nib_pow
    elif domain_size % 4 == 3:
        nib_pow = match_range(
            nibbles[last_k],
            range(0, 16),
            lambda v: whir_3_merkle_step_and_pow(v, last_state_in, last_path, prev_root, last_power_shift),
        )
        prod *= nib_pow

    return leaf_data, prod


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
    debug_assert(n_bits < 31)
    debug_assert(0 < n_bits)
    return match_range(
        n_bits,
        range(0, 1),
        lambda _: 0,
        range(1, 31),
        lambda i: checked_decompose_bits_small_value_const(to_decompose, i),
    )


@inline
def dot_product_ee_ret(a, b, n):
    res = Array(DIM)
    dot_product_ee(a, b, res, n)
    return res


@inline
def sum_continuous_ef(slice_ef, len):
    debug_assert(len <= NUM_REPEATED_ONES)
    res = Array(DIM)
    dot_product_be(REPEATED_ONES_PTR, slice_ef, res, len)
    return res


def mle_of_zeros_then_ones(point, n_zeros, n_vars):
    if n_vars == 0:
        res = Array(DIM)
        res[0] = 1 - n_zeros
        for i in unroll(1, DIM):
            res[i] = 0
        return res

    n_values = two_exp(n_vars)
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
    debug_assert(n < 32)
    debug_assert(n != 0)
    res = match_range(n, range(1, 32), lambda i: next_mle_const(x, y, i))
    return res

def next_mle_const(x, y, n: Const):
    # x and y are pointers to n elements of extension field

    # Build eq_prefix[0..n+1] where eq_prefix[i] = prod_{j<i} eq(x[j], y[j])
    # and eq(a,b) = a*b + (1-a)*(1-b)
    eq_prefix = Array((n + 1) * DIM)
    set_to_one(eq_prefix)
    for i in unroll(0, n):
        xi = x + i * DIM
        yi = y + i * DIM
        eq_i = Array(DIM)
        poly_eq_ee(xi, yi, eq_i)
        mul_extension(eq_prefix + i * DIM, eq_i, eq_prefix + (i + 1) * DIM)

    # Build low_suffix[0..n+1] where low_suffix[i] = prod_{j>=i} (x[j] * (1-y[j]))
    low_suffix = Array((n + 1) * DIM)
    set_to_one(low_suffix + n * DIM)
    for i in unroll(0, n):
        idx = n - 1 - i
        xi = x + idx * DIM
        yi = y + idx * DIM
        one_minus_y = one_minus_self_extension_ret(yi)
        x_one_minus_y = mul_extension_ret(xi, one_minus_y)
        mul_extension(low_suffix + (idx + 1) * DIM, x_one_minus_y, low_suffix + idx * DIM)

    # Compute sum = Σ_{arr=0..n} (eq_prefix[arr] * (1-x[arr]) * y[arr] * low_suffix[arr+1])
    sum: Mut = ZERO_VEC_PTR
    for arr in unroll(0, n):
        x_arr = x + arr * DIM
        y_arr = y + arr * DIM
        one_minus_x = one_minus_self_extension_ret(x_arr)
        carry = mul_extension_ret(one_minus_x, y_arr)
        eq_carry = mul_extension_ret(eq_prefix + arr * DIM, carry)
        term = mul_extension_ret(eq_carry, low_suffix + (arr + 1) * DIM)
        sum = add_extension_ret(sum, term)

    # Compute prod = product of all x[i] * product of all y[i]
    prod = mul_extension_ret(product_first_n_const(x, n), product_first_n_const(y, n))

    result = add_extension_ret(sum, prod)
    return result


def _verify_log2_small(n, partial_sums_24, log2: Const):
    # For log2 in [3, 23]: verify n has exactly log2 bits
    assert partial_sums_24[log2 - 1] == n
    assert partial_sums_24[log2 - 2] != n
    return


def _verify_log2_large(n, log2: Const):
    # For log2 in [24, 30]: verify 2^(log2-1) < n <= 2^log2
    # by checking that n - 2^(log2-1) - 1 fits in (log2-1) bits
    remainder = n - 2 ** (log2 - 1) - 1
    _unused = checked_decompose_bits_small_value_const(remainder, log2 - 1)
    return


def log2_ceil_runtime(n):
    # requires: 2 < n <= 2^30 (still inside HALF_BITS=32, so `_verify_log2_small`
    # is always chosen under Goldilocks).
    log2: Imu
    hint_log2_ceil(n, log2)
    assert log2 < 31
    if two_exp(log2) != n:
        _, partial_sums_low = checked_decompose_bits(n)
        match_range(log2, range(2, 31), lambda i: _verify_log2_small(n, partial_sums_low, i))
    return log2
