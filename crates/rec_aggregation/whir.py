from snark_lib import *
from fiat_shamir import *

WHIR_INITIAL_FOLDING_FACTOR = WHIR_INITIAL_FOLDING_FACTOR_PLACEHOLDER
MIN_WHIR_LOG_INV_RATE = MIN_WHIR_LOG_INV_RATE_PLACEHOLDER
MAX_WHIR_LOG_INV_RATE = MAX_WHIR_LOG_INV_RATE_PLACEHOLDER

# WHIR open configuration (filled at compilation time)
WHIR_OPEN_N_VARS = WHIR_OPEN_N_VARS_PLACEHOLDER
WHIR_OPEN_LOG_INV_RATE = WHIR_OPEN_LOG_INV_RATE_PLACEHOLDER

# Commitment level
WHIR_OPEN_COMMITMENT_OOD = WHIR_OPEN_COMMITMENT_OOD_PLACEHOLDER
WHIR_OPEN_STARTING_FGRIND = WHIR_OPEN_STARTING_FGRIND_PLACEHOLDER

# Round 0
WHIR_OPEN_R0_FOLD = WHIR_INITIAL_FOLDING_FACTOR
WHIR_OPEN_R0_QUERIES = WHIR_OPEN_R0_QUERIES_PLACEHOLDER
WHIR_OPEN_R0_OOD = WHIR_OPEN_R0_OOD_PLACEHOLDER
WHIR_OPEN_R0_QGRIND = WHIR_OPEN_R0_QGRIND_PLACEHOLDER
WHIR_OPEN_R0_FGRIND = WHIR_OPEN_R0_FGRIND_PLACEHOLDER
WHIR_OPEN_R0_DOMAIN_LOG = WHIR_OPEN_R0_DOMAIN_LOG_PLACEHOLDER
WHIR_OPEN_R0_FOLDED_DOMAIN_LOG = WHIR_OPEN_R0_FOLDED_DOMAIN_LOG_PLACEHOLDER
WHIR_OPEN_R0_LEAF_CHUNKS = WHIR_OPEN_R0_LEAF_CHUNKS_PLACEHOLDER
WHIR_OPEN_R0_SAMPLE_CHUNKS = WHIR_OPEN_R0_SAMPLE_CHUNKS_PLACEHOLDER

# Round 1
WHIR_OPEN_R1_FOLD = WHIR_OPEN_R1_FOLD_PLACEHOLDER
WHIR_OPEN_R1_QUERIES = WHIR_OPEN_R1_QUERIES_PLACEHOLDER
WHIR_OPEN_R1_OOD = WHIR_OPEN_R1_OOD_PLACEHOLDER
WHIR_OPEN_R1_QGRIND = WHIR_OPEN_R1_QGRIND_PLACEHOLDER
WHIR_OPEN_R1_FGRIND = WHIR_OPEN_R1_FGRIND_PLACEHOLDER
WHIR_OPEN_R1_DOMAIN_LOG = WHIR_OPEN_R1_DOMAIN_LOG_PLACEHOLDER
WHIR_OPEN_R1_FOLDED_DOMAIN_LOG = WHIR_OPEN_R1_FOLDED_DOMAIN_LOG_PLACEHOLDER
WHIR_OPEN_R1_LEAF_CHUNKS = WHIR_OPEN_R1_LEAF_CHUNKS_PLACEHOLDER
WHIR_OPEN_R1_SAMPLE_CHUNKS = WHIR_OPEN_R1_SAMPLE_CHUNKS_PLACEHOLDER

# Final round
WHIR_OPEN_FINAL_FOLD = WHIR_OPEN_R1_FOLD
WHIR_OPEN_FINAL_QUERIES = WHIR_OPEN_FINAL_QUERIES_PLACEHOLDER
WHIR_OPEN_FINAL_QGRIND = WHIR_OPEN_FINAL_QGRIND_PLACEHOLDER
WHIR_OPEN_FINAL_DOMAIN_LOG = WHIR_OPEN_FINAL_DOMAIN_LOG_PLACEHOLDER
WHIR_OPEN_FINAL_FOLDED_DOMAIN_LOG = WHIR_OPEN_FINAL_FOLDED_DOMAIN_LOG_PLACEHOLDER
WHIR_OPEN_FINAL_LEAF_CHUNKS = WHIR_OPEN_R1_LEAF_CHUNKS
WHIR_OPEN_FINAL_SAMPLE_CHUNKS = WHIR_OPEN_FINAL_SAMPLE_CHUNKS_PLACEHOLDER

# Final polynomial
WHIR_OPEN_N_FINAL_VARS = WHIR_OPEN_N_FINAL_VARS_PLACEHOLDER
WHIR_OPEN_FINAL_COEFFS_CHUNKS = WHIR_OPEN_FINAL_COEFFS_CHUNKS_PLACEHOLDER

# Derived constants
WHIR_OPEN_R0_N_COMBINATION = WHIR_OPEN_R0_OOD + WHIR_OPEN_R0_QUERIES
WHIR_OPEN_R1_N_COMBINATION = WHIR_OPEN_R1_OOD + WHIR_OPEN_R1_QUERIES
WHIR_OPEN_R0_N_VARS_REMAINING = WHIR_OPEN_N_VARS - WHIR_OPEN_R0_FOLD
WHIR_OPEN_R1_N_VARS_REMAINING = WHIR_OPEN_R0_N_VARS_REMAINING - WHIR_OPEN_R1_FOLD
WHIR_OPEN_R0_R1_FOLD_SUM = WHIR_OPEN_R0_FOLD + WHIR_OPEN_R1_FOLD
WHIR_OPEN_ALL_FOLD_SUM = WHIR_OPEN_R0_R1_FOLD_SUM + WHIR_OPEN_FINAL_FOLD
WHIR_OPEN_2_POW_N_FINAL_VARS = 2 ** WHIR_OPEN_N_FINAL_VARS


@inline
def fs_receive_chunks_inlined(fs, n_chunks):
    new_fs = Array(1 + 8 * n_chunks)
    transcript_ptr = fs[8]
    new_fs[8 * n_chunks] = transcript_ptr + 8 * n_chunks
    poseidon16_compress(fs, transcript_ptr, new_fs)
    for i in unroll(1, n_chunks):
        poseidon16_compress(
            new_fs + ((i - 1) * 8),
            transcript_ptr + i * 8,
            new_fs + i * 8,
        )
    return new_fs + 8 * (n_chunks - 1), transcript_ptr


@inline
def fs_sample_chunks_inlined(fs, n_chunks):
    sampled = Array((n_chunks + 1) * 8 + 1)
    for i in unroll(0, n_chunks + 1):
        domain_sep = Array(8)
        domain_sep[0] = i
        set_to_7_zeros(domain_sep + 1)
        poseidon16_compress(domain_sep, fs, sampled + i * 8)
    sampled[(n_chunks + 1) * 8] = fs[8]
    new_fs = sampled + n_chunks * 8
    return new_fs, sampled


@inline
def fs_receive_ef_deep_inlined(fs, n):
    new_fs, ef_ptr = fs_receive_chunks_inlined(fs, div_ceil(n * DIM, 8))
    for i in unroll(n * DIM, next_multiple_of(n * DIM, 8)):
        assert ef_ptr[i] == 0
    return new_fs, ef_ptr


@inline
def powers_inlined(alpha, n):
    res = Array(n * DIM)
    set_to_one(res)
    for i in unroll(0, n - 1):
        mul_extension(res + i * DIM, alpha, res + (i + 1) * DIM)
    return res


@inline
def expand_from_univariate_base_inlined(alpha, n):
    res = Array(n)
    current: Mut = alpha
    for i in unroll(0, n):
        res[i] = current
        current *= current
    return res


@inline
def expand_from_univariate_ext_inlined(alpha, n):
    res = Array(n * DIM)
    copy_5(alpha, res)
    for i in unroll(0, n - 1):
        mul_extension(res + i * DIM, res + i * DIM, res + (i + 1) * DIM)
    return res


@inline
def poly_eq_extension_inlined(point, n):
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


@inline
def eval_multilinear_coeffs_rev_inlined(coeffs, point, n):
    basis = Array(2**n * DIM)
    set_to_one(basis)
    for k in unroll(0, n):
        for j in unroll(0, 2**k):
            mul_extension(basis + j * DIM, point + k * DIM, basis + (j + 2**k) * DIM)
    result = Array(DIM)
    dot_product_ee(coeffs, basis, result, 2**n)
    return result


@inline
def fs_sample_data_inlined(fs, n_chunks, offset):
    sampled = Array(n_chunks * 8)
    for i in unroll(0, n_chunks):
        domain_sep = Array(8)
        domain_sep[0] = offset + i
        set_to_7_zeros(domain_sep + 1)
        poseidon16_compress(domain_sep, fs, sampled + i * 8)
    return sampled


@inline
def fs_finalize_sample_inlined(fs, total_n_chunks):
    new_fs = Array(9)
    domain_sep = Array(8)
    domain_sep[0] = total_n_chunks
    set_to_7_zeros(domain_sep + 1)
    poseidon16_compress(domain_sep, fs, new_fs)
    new_fs[8] = fs[8]
    return new_fs


def whir_open(
    fs: Mut,
    n_vars,
    initial_log_inv_rate,
    root: Mut,
    ood_points_commit,
    combination_randomness_powers_0,
    claimed_sum: Mut,
):
    assert n_vars == WHIR_OPEN_N_VARS
    assert initial_log_inv_rate == WHIR_OPEN_LOG_INV_RATE

    all_folding_randomness = Array(4)
    all_ood_points = Array(2)
    all_circle_values = Array(3)
    all_combination_randomness_powers = Array(2)

    # Round 0
    (
        fs,
        all_folding_randomness[0],
        all_ood_points[0],
        root,
        all_circle_values[0],
        all_combination_randomness_powers[0],
        claimed_sum,
    ) = whir_round_0(fs, root, claimed_sum)

    # Round 1
    (
        fs,
        all_folding_randomness[1],
        all_ood_points[1],
        root,
        all_circle_values[1],
        all_combination_randomness_powers[1],
        claimed_sum,
    ) = whir_round_1(fs, root, claimed_sum)

    # Final folding sumcheck inlined (n_steps=WHIR_OPEN_FINAL_FOLD, degree=2)
    folding_challenges_2 = Array(WHIR_OPEN_FINAL_FOLD * DIM)
    all_folding_randomness[2] = folding_challenges_2
    for sc_round in unroll(0, WHIR_OPEN_FINAL_FOLD):
        fs, poly = fs_receive_ef_deep_inlined(fs, 3)
        sum_over_boolean_hypercube = polynomial_sum_at_0_and_1(poly, 2)
        copy_5(sum_over_boolean_hypercube, claimed_sum)
        fs = fs_grinding(fs, WHIR_OPEN_R1_FGRIND)
        fs, rand = fs_sample_ef(fs)
        claimed_sum = univariate_polynomial_eval(poly, rand, 2)
        copy_5(rand, folding_challenges_2 + sc_round * DIM)

    # Receive final coefficients
    fs, final_coefficients = fs_receive_chunks_inlined(fs, WHIR_OPEN_FINAL_COEFFS_CHUNKS)

    # Final STIR queries
    fs, all_circle_values[2], final_folds = sample_stir_indexes_and_fold_final(fs, root, all_folding_randomness[2])

    # Evaluate final polynomial on circle
    final_circle_values = all_circle_values[2]
    for i in unroll(0, WHIR_OPEN_FINAL_QUERIES):
        alpha = final_circle_values[i]
        alpha_powers = Array(WHIR_OPEN_2_POW_N_FINAL_VARS)
        alpha_powers[0] = 1
        for k in unroll(0, WHIR_OPEN_2_POW_N_FINAL_VARS - 1):
            alpha_powers[k + 1] = alpha_powers[k] * alpha
        dot_product_be(alpha_powers, final_coefficients, final_folds + i * DIM, WHIR_OPEN_2_POW_N_FINAL_VARS)

    # Final sumcheck inlined (n_steps=WHIR_OPEN_N_FINAL_VARS, degree=2)
    folding_challenges_3 = Array(WHIR_OPEN_N_FINAL_VARS * DIM)
    all_folding_randomness[3] = folding_challenges_3
    end_sum: Mut = claimed_sum
    for sc_round in unroll(0, WHIR_OPEN_N_FINAL_VARS):
        fs, poly = fs_receive_ef_deep_inlined(fs, 3)
        sum_over_boolean_hypercube = polynomial_sum_at_0_and_1(poly, 2)
        copy_5(sum_over_boolean_hypercube, end_sum)
        fs, rand = fs_sample_ef(fs)
        end_sum = univariate_polynomial_eval(poly, rand, 2)
        copy_5(rand, folding_challenges_3 + sc_round * DIM)

    # Assemble folding_randomness_global
    folding_randomness_global = Array(WHIR_OPEN_N_VARS * DIM)
    # Round 0 challenges
    for j in unroll(0, WHIR_OPEN_R0_FOLD):
        copy_5(all_folding_randomness[0] + j * DIM, folding_randomness_global + j * DIM)
    # Round 1 challenges
    for j in unroll(0, WHIR_OPEN_R1_FOLD):
        copy_5(all_folding_randomness[1] + j * DIM, folding_randomness_global + (WHIR_OPEN_R0_FOLD + j) * DIM)
    # Final folding challenges
    for j in unroll(0, WHIR_OPEN_FINAL_FOLD):
        copy_5(all_folding_randomness[2] + j * DIM, folding_randomness_global + (WHIR_OPEN_R0_R1_FOLD_SUM + j) * DIM)
    # Final sumcheck challenges
    for j in unroll(0, WHIR_OPEN_N_FINAL_VARS):
        copy_5(all_folding_randomness[3] + j * DIM, folding_randomness_global + (WHIR_OPEN_ALL_FOLD_SUM + j) * DIM)

    # OOD recovery at commitment
    all_ood_recovered_evals = Array(WHIR_OPEN_COMMITMENT_OOD * DIM)
    for i in unroll(0, WHIR_OPEN_COMMITMENT_OOD):
        expanded_from_univariate = expand_from_univariate_ext_inlined(ood_points_commit + i * DIM, WHIR_OPEN_N_VARS)
        poly_eq_ee(expanded_from_univariate, folding_randomness_global, all_ood_recovered_evals + i * DIM, WHIR_OPEN_N_VARS)
    s: Mut = Array(DIM)
    dot_product_ee(all_ood_recovered_evals, combination_randomness_powers_0, s, WHIR_OPEN_COMMITMENT_OOD)

    # Round 0 consistency
    my_folding_randomness_0 = folding_randomness_global + WHIR_OPEN_R0_FOLD * DIM
    combination_randomness_powers_r0 = all_combination_randomness_powers[0]
    # Single OOD point (dot_product_ee with n=1 and powers[0]=1 is identity)
    expanded_ood_0 = expand_from_univariate_ext_inlined(all_ood_points[0], WHIR_OPEN_R0_N_VARS_REMAINING)
    summed_ood_0 = Array(DIM)
    poly_eq_ee(expanded_ood_0, my_folding_randomness_0, summed_ood_0, WHIR_OPEN_R0_N_VARS_REMAINING)
    # Query checks
    s6s_0 = Array(WHIR_OPEN_R0_QUERIES * DIM)
    circle_value_0 = all_circle_values[0]
    for j in unroll(0, WHIR_OPEN_R0_QUERIES):
        expanded_q = expand_from_univariate_base_inlined(circle_value_0[j], WHIR_OPEN_R0_N_VARS_REMAINING)
        poly_eq_be(expanded_q, my_folding_randomness_0, s6s_0 + j * DIM, WHIR_OPEN_R0_N_VARS_REMAINING)
    s7_0 = Array(DIM)
    dot_product_ee(s6s_0, combination_randomness_powers_r0 + WHIR_OPEN_R0_OOD * DIM, s7_0, WHIR_OPEN_R0_QUERIES)
    s = add_extension_ret(s, s7_0)
    s = add_extension_ret(summed_ood_0, s)

    # Round 1 consistency
    my_folding_randomness_1 = folding_randomness_global + WHIR_OPEN_R0_R1_FOLD_SUM * DIM
    combination_randomness_powers_r1 = all_combination_randomness_powers[1]
    # OOD points
    my_ood_recovered_evals_1 = Array(WHIR_OPEN_R1_OOD * DIM)
    for j in unroll(0, WHIR_OPEN_R1_OOD):
        expanded_ood_1 = expand_from_univariate_ext_inlined(all_ood_points[1] + j * DIM, WHIR_OPEN_R1_N_VARS_REMAINING)
        poly_eq_ee(expanded_ood_1, my_folding_randomness_1, my_ood_recovered_evals_1 + j * DIM, WHIR_OPEN_R1_N_VARS_REMAINING)
    summed_ood_1 = Array(DIM)
    dot_product_ee(my_ood_recovered_evals_1, combination_randomness_powers_r1, summed_ood_1, WHIR_OPEN_R1_OOD)
    # Query checks
    s6s_1 = Array(WHIR_OPEN_R1_QUERIES * DIM)
    circle_value_1 = all_circle_values[1]
    for j in unroll(0, WHIR_OPEN_R1_QUERIES):
        expanded_q = expand_from_univariate_base_inlined(circle_value_1[j], WHIR_OPEN_R1_N_VARS_REMAINING)
        poly_eq_be(expanded_q, my_folding_randomness_1, s6s_1 + j * DIM, WHIR_OPEN_R1_N_VARS_REMAINING)
    s7_1 = Array(DIM)
    dot_product_ee(s6s_1, combination_randomness_powers_r1 + WHIR_OPEN_R1_OOD * DIM, s7_1, WHIR_OPEN_R1_QUERIES)
    s = add_extension_ret(s, s7_1)
    s = add_extension_ret(summed_ood_1, s)

    # Final value
    final_value = eval_multilinear_coeffs_rev_inlined(final_coefficients, all_folding_randomness[3], WHIR_OPEN_N_FINAL_VARS)

    return fs, folding_randomness_global, s, final_value, end_sum








def sample_stir_indexes_and_fold_r0(fs: Mut, prev_root, folding_randomness):
    # Round 0: basefield leaves
    fs = fs_grinding(fs, WHIR_OPEN_R0_QGRIND)
    sampled = fs_sample_data_inlined(fs, WHIR_OPEN_R0_SAMPLE_CHUNKS, 0)
    fs = fs_finalize_sample_inlined(fs, WHIR_OPEN_R0_SAMPLE_CHUNKS)
    merkle_leaves = Array(WHIR_OPEN_R0_QUERIES)
    circle_values = Array(WHIR_OPEN_R0_QUERIES)
    for i in unroll(0, WHIR_OPEN_R0_QUERIES):
        nibbles, circle_values[i] = checked_decompose_bits_and_compute_root_pow_const(sampled[i], WHIR_OPEN_R0_FOLDED_DOMAIN_LOG)
        merkle_leaves[i] = hash_and_verify_merkle_hint(nibbles, prev_root, WHIR_OPEN_R0_FOLDED_DOMAIN_LOG, WHIR_OPEN_R0_LEAF_CHUNKS)
    folds = Array(WHIR_OPEN_R0_QUERIES * DIM)
    poly_eq = poly_eq_extension_inlined(folding_randomness, WHIR_OPEN_R0_FOLD)
    for i in unroll(0, WHIR_OPEN_R0_QUERIES):
        dot_product_be(merkle_leaves[i], poly_eq, folds + i * DIM, 2 ** WHIR_OPEN_R0_FOLD)
    return fs, circle_values, folds


def sample_stir_indexes_and_fold_r1(fs: Mut, prev_root, folding_randomness):
    # Round 1: extension field leaves
    fs = fs_grinding(fs, WHIR_OPEN_R1_QGRIND)
    sampled = fs_sample_data_inlined(fs, WHIR_OPEN_R1_SAMPLE_CHUNKS, 0)
    fs = fs_finalize_sample_inlined(fs, WHIR_OPEN_R1_SAMPLE_CHUNKS)
    merkle_leaves = Array(WHIR_OPEN_R1_QUERIES)
    circle_values = Array(WHIR_OPEN_R1_QUERIES)
    for i in unroll(0, WHIR_OPEN_R1_QUERIES):
        nibbles, circle_values[i] = checked_decompose_bits_and_compute_root_pow_const(sampled[i], WHIR_OPEN_R1_FOLDED_DOMAIN_LOG)
        merkle_leaves[i] = hash_and_verify_merkle_hint(nibbles, prev_root, WHIR_OPEN_R1_FOLDED_DOMAIN_LOG, WHIR_OPEN_R1_LEAF_CHUNKS)
    folds = Array(WHIR_OPEN_R1_QUERIES * DIM)
    poly_eq = poly_eq_extension_inlined(folding_randomness, WHIR_OPEN_R1_FOLD)
    for i in unroll(0, WHIR_OPEN_R1_QUERIES):
        dot_product_ee(merkle_leaves[i], poly_eq, folds + i * DIM, 2 ** WHIR_OPEN_R1_FOLD)
    return fs, circle_values, folds


def sample_stir_indexes_and_fold_final(fs: Mut, prev_root, folding_randomness):
    # Final: extension field leaves
    fs = fs_grinding(fs, WHIR_OPEN_FINAL_QGRIND)
    sampled = fs_sample_data_inlined(fs, WHIR_OPEN_FINAL_SAMPLE_CHUNKS, 0)
    fs = fs_finalize_sample_inlined(fs, WHIR_OPEN_FINAL_SAMPLE_CHUNKS)
    merkle_leaves = Array(WHIR_OPEN_FINAL_QUERIES)
    circle_values = Array(WHIR_OPEN_FINAL_QUERIES)
    for i in unroll(0, WHIR_OPEN_FINAL_QUERIES):
        nibbles, circle_values[i] = checked_decompose_bits_and_compute_root_pow_const(sampled[i], WHIR_OPEN_FINAL_FOLDED_DOMAIN_LOG)
        merkle_leaves[i] = hash_and_verify_merkle_hint(nibbles, prev_root, WHIR_OPEN_FINAL_FOLDED_DOMAIN_LOG, WHIR_OPEN_FINAL_LEAF_CHUNKS)
    folds = Array(WHIR_OPEN_FINAL_QUERIES * DIM)
    poly_eq = poly_eq_extension_inlined(folding_randomness, WHIR_OPEN_FINAL_FOLD)
    for i in unroll(0, WHIR_OPEN_FINAL_QUERIES):
        dot_product_ee(merkle_leaves[i], poly_eq, folds + i * DIM, 2 ** WHIR_OPEN_FINAL_FOLD)
    return fs, circle_values, folds


def whir_round_0(fs: Mut, prev_root, claimed_sum):
    # Round 0: sumcheck_verify inlined (n_steps=WHIR_OPEN_R0_FOLD, degree=2)
    folding_randomness = Array(WHIR_OPEN_R0_FOLD * DIM)
    new_claimed_sum_a: Mut = claimed_sum
    for sc_round in unroll(0, WHIR_OPEN_R0_FOLD):
        fs, poly = fs_receive_ef_deep_inlined(fs, 3)
        sum_over_boolean_hypercube = polynomial_sum_at_0_and_1(poly, 2)
        copy_5(sum_over_boolean_hypercube, new_claimed_sum_a)
        fs = fs_grinding(fs, WHIR_OPEN_STARTING_FGRIND)
        fs, rand = fs_sample_ef(fs)
        new_claimed_sum_a = univariate_polynomial_eval(poly, rand, 2)
        copy_5(rand, folding_randomness + sc_round * DIM)

    # parse_whir_commitment inlined (num_ood=WHIR_OPEN_R0_OOD)
    fs, root = fs_receive_chunks_inlined(fs, 1)
    fs, ood_points = fs_sample_chunks_inlined(fs, WHIR_OPEN_R0_OOD)
    fs, ood_evals = fs_receive_ef_deep_inlined(fs, WHIR_OPEN_R0_OOD)

    fs, circle_values, folds = sample_stir_indexes_and_fold_r0(fs, prev_root, folding_randomness)

    fs, combination_randomness_gen = fs_sample_ef(fs)
    combination_randomness_powers = powers_inlined(combination_randomness_gen, WHIR_OPEN_R0_N_COMBINATION)

    # dot_product_ee(ood_evals, powers, res, 1) = ood_evals[0] * powers[0] = ood_evals (powers[0]=1)
    claimed_sum_1 = Array(DIM)
    dot_product_ee(folds, combination_randomness_powers + WHIR_OPEN_R0_OOD * DIM, claimed_sum_1, WHIR_OPEN_R0_QUERIES)

    new_claimed_sum_b = add_extension_ret(ood_evals, claimed_sum_1)
    final_sum = add_extension_ret(new_claimed_sum_a, new_claimed_sum_b)

    return (fs, folding_randomness, ood_points, root, circle_values, combination_randomness_powers, final_sum)


def whir_round_1(fs: Mut, prev_root, claimed_sum):
    # Round 1: sumcheck_verify inlined (n_steps=WHIR_OPEN_R1_FOLD, degree=2)
    folding_randomness = Array(WHIR_OPEN_R1_FOLD * DIM)
    new_claimed_sum_a: Mut = claimed_sum
    for sc_round in unroll(0, WHIR_OPEN_R1_FOLD):
        fs, poly = fs_receive_ef_deep_inlined(fs, 3)
        sum_over_boolean_hypercube = polynomial_sum_at_0_and_1(poly, 2)
        copy_5(sum_over_boolean_hypercube, new_claimed_sum_a)
        fs = fs_grinding(fs, WHIR_OPEN_R0_FGRIND)
        fs, rand = fs_sample_ef(fs)
        new_claimed_sum_a = univariate_polynomial_eval(poly, rand, 2)
        copy_5(rand, folding_randomness + sc_round * DIM)

    # parse_whir_commitment inlined (num_ood=WHIR_OPEN_R1_OOD)
    fs, root = fs_receive_chunks_inlined(fs, 1)
    fs, ood_points = fs_sample_chunks_inlined(fs, WHIR_OPEN_R1_OOD)
    fs, ood_evals = fs_receive_ef_deep_inlined(fs, WHIR_OPEN_R1_OOD)

    fs, circle_values, folds = sample_stir_indexes_and_fold_r1(fs, prev_root, folding_randomness)

    fs, combination_randomness_gen = fs_sample_ef(fs)
    combination_randomness_powers = powers_inlined(combination_randomness_gen, WHIR_OPEN_R1_N_COMBINATION)

    claimed_sum_0 = Array(DIM)
    dot_product_ee(ood_evals, combination_randomness_powers, claimed_sum_0, WHIR_OPEN_R1_OOD)

    claimed_sum_1 = Array(DIM)
    dot_product_ee(folds, combination_randomness_powers + WHIR_OPEN_R1_OOD * DIM, claimed_sum_1, WHIR_OPEN_R1_QUERIES)

    new_claimed_sum_b = add_extension_ret(claimed_sum_0, claimed_sum_1)
    final_sum = add_extension_ret(new_claimed_sum_a, new_claimed_sum_b)

    return (fs, folding_randomness, ood_points, root, circle_values, combination_randomness_powers, final_sum)


@inline
def polynomial_sum_at_0_and_1(coeffs, degree):
    debug_assert(1 < degree)
    debug_assert(degree + 1 <= NUM_REPEATED_ONES_IN_RESERVED_MEMORY)
    res = Array(DIM)
    dot_product_be(REPEATED_ONES_PTR, coeffs, res, degree + 1)
    return add_extension_ret(res, coeffs)





@inline
def get_num_oods(log_inv_rate, n_vars):
    assert log_inv_rate == WHIR_OPEN_LOG_INV_RATE
    assert n_vars == WHIR_OPEN_N_VARS
    num_oods = Array(3)
    num_oods[0] = WHIR_OPEN_COMMITMENT_OOD
    num_oods[1] = WHIR_OPEN_R0_OOD
    num_oods[2] = WHIR_OPEN_R1_OOD
    return num_oods
