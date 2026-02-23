from snark_lib import *
from fiat_shamir import *

WHIR_INITIAL_FOLDING_FACTOR = WHIR_INITIAL_FOLDING_FACTOR_PLACEHOLDER
WHIR_SUBSEQUENT_FOLDING_FACTOR = WHIR_SUBSEQUENT_FOLDING_FACTOR_PLACEHOLDER
WHIR_FIRST_RS_REDUCTION_FACTOR = WHIR_FIRST_RS_REDUCTION_FACTOR_PLACEHOLDER
MIN_WHIR_LOG_INV_RATE = MIN_WHIR_LOG_INV_RATE_PLACEHOLDER
MAX_WHIR_LOG_INV_RATE = MAX_WHIR_LOG_INV_RATE_PLACEHOLDER
MAX_NUM_VARIABLES_TO_SEND_COEFFS = MAX_NUM_VARIABLES_TO_SEND_COEFFS_PLACEHOLDER

WHIR_ALL_POTENTIAL_NUM_QUERIES = WHIR_ALL_POTENTIAL_NUM_QUERIES_PLACEHOLDER
WHIR_ALL_POTENTIAL_QUERY_GRINDING = WHIR_ALL_POTENTIAL_QUERY_GRINDING_PLACEHOLDER
WHIR_ALL_POTENTIAL_NUM_OODS = WHIR_ALL_POTENTIAL_NUM_OODS_PLACEHOLDER
WHIR_ALL_POTENTIAL_FOLDING_GRINDING = WHIR_ALL_POTENTIAL_FOLDING_GRINDING_PLACEHOLDER
MIN_STACKED_N_VARS = MIN_STACKED_N_VARS_PLACEHOLDER

def whir_open(
    fs: Mut,
    n_vars,
    initial_log_inv_rate,
    root: Mut,
    ood_points_commit,
    combination_randomness_powers_0,
    claimed_sum: Mut,
):
    n_rounds, n_final_vars, num_queries, num_oods, query_grinding_bits, folding_grinding = get_whir_params(n_vars, initial_log_inv_rate)
    folding_factors = Array(n_rounds + 1)
    folding_factors[0] = WHIR_INITIAL_FOLDING_FACTOR
    for i in range(1, n_rounds + 1):
        folding_factors[i] = WHIR_SUBSEQUENT_FOLDING_FACTOR
    
    all_folding_randomness = Array(n_rounds + 2)
    all_ood_points = Array(n_rounds)
    all_circle_values = Array(n_rounds + 1)
    all_combination_randomness_powers = Array(n_rounds)

    domain_sz: Mut = n_vars + initial_log_inv_rate
    for r in range(0, n_rounds):
        is_first_round: Imu
        if r == 0:
            is_first_round = 1
        else:
            is_first_round = 0
        (
            fs,
            all_folding_randomness[r],
            all_ood_points[r],
            root,
            all_circle_values[r],
            all_combination_randomness_powers[r],
            claimed_sum,
        ) = whir_round(
            fs,
            root,
            folding_factors[r],
            powers_of_two(folding_factors[r]),
            is_first_round,
            num_queries[r],
            domain_sz,
            claimed_sum,
            query_grinding_bits[r],
            num_oods[r + 1],
            folding_grinding[r],
        )
        if r == 0:
            domain_sz -= WHIR_FIRST_RS_REDUCTION_FACTOR
        else:
            domain_sz -= 1

    fs, all_folding_randomness[n_rounds], claimed_sum = sumcheck_verify_with_grinding(
        fs, WHIR_SUBSEQUENT_FOLDING_FACTOR, claimed_sum, 2, folding_grinding[n_rounds]
    )

    fs, final_coeffcients = fs_receive_ef_by_log_dynamic(fs, n_final_vars, MAX_NUM_VARIABLES_TO_SEND_COEFFS - WHIR_SUBSEQUENT_FOLDING_FACTOR, MAX_NUM_VARIABLES_TO_SEND_COEFFS+ 1)

    fs, all_circle_values[n_rounds], final_folds = sample_stir_indexes_and_fold(
        fs,
        num_queries[n_rounds],
        0,
        WHIR_SUBSEQUENT_FOLDING_FACTOR,
        2 ** WHIR_SUBSEQUENT_FOLDING_FACTOR,
        domain_sz,
        root,
        all_folding_randomness[n_rounds],
        query_grinding_bits[n_rounds],
    )

    final_circle_values = all_circle_values[n_rounds]
    for i in range(0, num_queries[n_rounds]):
        alpha = final_circle_values[i]
        final_pol_evaluated_on_circle = match_range(n_final_vars, range(MAX_NUM_VARIABLES_TO_SEND_COEFFS - WHIR_SUBSEQUENT_FOLDING_FACTOR, MAX_NUM_VARIABLES_TO_SEND_COEFFS + 1), lambda n: univariate_eval_on_base(final_coeffcients, alpha, n))
        copy_5(final_pol_evaluated_on_circle, final_folds + i * DIM)

    fs, all_folding_randomness[n_rounds + 1], end_sum = sumcheck_verify(fs, n_final_vars, claimed_sum, 2)

    folding_randomness_global = Array(n_vars * DIM)

    start: Mut = folding_randomness_global
    for i in range(0, n_rounds + 1):
        for j in range(0, folding_factors[i]):
            copy_5(all_folding_randomness[i] + j * DIM, start + j * DIM)
        start += folding_factors[i] * DIM
    for j in range(0, n_final_vars):
        copy_5(all_folding_randomness[n_rounds + 1] + j * DIM, start + j * DIM)

    all_ood_recovered_evals = Array(num_oods[0] * DIM)
    for i in range(0, num_oods[0]):
        expanded_from_univariate = expand_from_univariate_ext(ood_points_commit + i * DIM, n_vars)
        ood_rec = eq_mle_extension(expanded_from_univariate, folding_randomness_global, n_vars)
        copy_5(ood_rec, all_ood_recovered_evals + i * DIM)
    s: Mut = Array(DIM)
    dot_product_ee_dynamic(
        all_ood_recovered_evals,
        combination_randomness_powers_0,
        s,
        num_oods[0],
    )

    n_vars_remaining: Mut = n_vars
    my_folding_randomness: Mut = folding_randomness_global
    for i in range(0, n_rounds):
        n_vars_remaining -= folding_factors[i]
        my_ood_recovered_evals = Array(num_oods[i + 1] * DIM)
        combination_randomness_powers = all_combination_randomness_powers[i]
        my_folding_randomness += folding_factors[i] * DIM
        for j in range(0, num_oods[i + 1]):
            expanded_from_univariate = expand_from_univariate_ext(all_ood_points[i] + j * DIM, n_vars_remaining)
            ood_rec = eq_mle_extension(expanded_from_univariate, my_folding_randomness, n_vars_remaining)
            copy_5(ood_rec, my_ood_recovered_evals + j * DIM)
        summed_ood = Array(DIM)
        dot_product_ee_dynamic(
            my_ood_recovered_evals,
            combination_randomness_powers,
            summed_ood,
            num_oods[i + 1],
        )

        s6s = Array((num_queries[i]) * DIM)
        circle_value_i = all_circle_values[i]
        for j in range(0, num_queries[i]):  # unroll ?
            expanded_from_univariate = expand_from_univariate_base(circle_value_i[j], n_vars_remaining)
            temp = eq_mle_base_extension(expanded_from_univariate, my_folding_randomness, n_vars_remaining)
            copy_5(temp, s6s + j * DIM)
        s7 = Array(DIM)
        dot_product_ee_dynamic(
            s6s,
            combination_randomness_powers + num_oods[i + 1] * DIM,
            s7,
            num_queries[i],
        )
        s = add_extension_ret(s, s7)
        s = add_extension_ret(summed_ood, s)
    final_value = match_range(n_final_vars, range(MAX_NUM_VARIABLES_TO_SEND_COEFFS - WHIR_SUBSEQUENT_FOLDING_FACTOR, MAX_NUM_VARIABLES_TO_SEND_COEFFS + 1), lambda n: eval_multilinear_coeffs_rev(final_coeffcients, all_folding_randomness[n_rounds + 1], n))
    # copy_5(mul_extension_ret(s, final_value), end_sum);

    return fs, folding_randomness_global, s, final_value, end_sum


def sumcheck_verify(fs: Mut, n_steps, claimed_sum, degree: Const):
    challenges = Array(n_steps * DIM)
    fs, new_claimed_sum = sumcheck_verify_helper(fs, n_steps, claimed_sum, degree, challenges)
    return fs, challenges, new_claimed_sum


def sumcheck_verify_helper(fs: Mut, n_steps, claimed_sum: Mut, degree: Const, challenges):
    for sc_round in range(0, n_steps):
        fs, poly = fs_receive_ef_inlined(fs, degree + 1)
        sum_over_boolean_hypercube = polynomial_sum_at_0_and_1(poly, degree)
        copy_5(sum_over_boolean_hypercube, claimed_sum)
        fs, rand = fs_sample_ef(fs)
        claimed_sum = univariate_polynomial_eval(poly, rand, degree)
        copy_5(rand, challenges + sc_round * DIM)

    return fs, claimed_sum


def sumcheck_verify_with_grinding(fs: Mut, n_steps, claimed_sum: Mut, degree: Const, folding_grinding_bits):
    challenges = Array(n_steps * DIM)
    for sc_round in range(0, n_steps):
        fs, poly = fs_receive_ef_inlined(fs, degree + 1)
        sum_over_boolean_hypercube = polynomial_sum_at_0_and_1(poly, degree)
        copy_5(sum_over_boolean_hypercube, claimed_sum)
        fs = fs_grinding(fs, folding_grinding_bits)
        fs, rand = fs_sample_ef(fs)
        claimed_sum = univariate_polynomial_eval(poly, rand, degree)
        copy_5(rand, challenges + sc_round * DIM)

    return fs, challenges, claimed_sum


def sample_stir_indexes_and_fold(
    fs: Mut,
    num_queries,
    merkle_leaves_in_basefield,
    folding_factor,
    two_pow_folding_factor,
    domain_size,
    prev_root,
    folding_randomness,
    query_grinding_bits,
):
    folded_domain_size = domain_size - folding_factor

    fs = fs_grinding(fs, query_grinding_bits)
    fs, stir_challenges_indexes, circle_values = sample_bits_and_compute_root_pow(fs, num_queries, folded_domain_size)

    answers = Array(num_queries)

    n_chunks_per_answer: Imu
    # the number of chunk of 8 field elements per merkle leaf opened
    if merkle_leaves_in_basefield == 1:
        n_chunks_per_answer = two_pow_folding_factor
    else:
        n_chunks_per_answer = two_pow_folding_factor * DIM

    hash_and_verify_merkle_batch_hint(
        num_queries, answers, stir_challenges_indexes, prev_root,
        folded_domain_size, n_chunks_per_answer / DIGEST_LEN,
    )

    folds = Array(num_queries * DIM)

    poly_eq = poly_eq_extension_dynamic(folding_randomness, folding_factor)

    if merkle_leaves_in_basefield == 1:
        for i in range(0, num_queries):
            dot_product_be_dynamic(answers[i], poly_eq, folds + i * DIM, two_pow_folding_factor)
    else:
        for i in range(0, num_queries):
            dot_product_ee_dynamic(answers[i], poly_eq, folds + i * DIM, two_pow_folding_factor)

    return fs, circle_values, folds


def whir_round(
    fs: Mut,
    prev_root,
    folding_factor,
    two_pow_folding_factor,
    merkle_leaves_in_basefield,
    num_queries,
    domain_size,
    claimed_sum,
    query_grinding_bits,
    num_ood,
    folding_grinding_bits,
):
    fs, folding_randomness, new_claimed_sum_a = sumcheck_verify_with_grinding(fs, folding_factor, claimed_sum, 2, folding_grinding_bits)

    fs, root, ood_points, ood_evals = parse_commitment(fs, num_ood)

    fs, circle_values, folds = sample_stir_indexes_and_fold(
        fs,
        num_queries,
        merkle_leaves_in_basefield,
        folding_factor,
        two_pow_folding_factor,
        domain_size,
        prev_root,
        folding_randomness,
        query_grinding_bits,
    )

    fs, combination_randomness_gen = fs_sample_ef(fs)

    combination_randomness_powers = powers(combination_randomness_gen, num_queries + num_ood)

    claimed_sum_0 = Array(DIM)
    dot_product_ee_dynamic(ood_evals, combination_randomness_powers, claimed_sum_0, num_ood)

    claimed_sum_1 = Array(DIM)
    dot_product_ee_dynamic(folds, combination_randomness_powers + num_ood * DIM, claimed_sum_1, num_queries)

    new_claimed_sum_b = add_extension_ret(claimed_sum_0, claimed_sum_1)

    final_sum = add_extension_ret(new_claimed_sum_a, new_claimed_sum_b)

    return (
        fs,
        folding_randomness,
        ood_points,
        root,
        circle_values,
        combination_randomness_powers,
        final_sum,
    )


@inline
def polynomial_sum_at_0_and_1(coeffs, degree):
    debug_assert(1 < degree)
    return add_extension_ret(sum_continuous_ef(coeffs, degree + 1), coeffs)


def parse_commitment(fs: Mut, num_ood):
    root: Imu
    ood_points: Imu
    ood_evals: Imu
    debug_assert(num_ood < 4)
    debug_assert(num_ood != 0)
    fs, root, ood_points, ood_evals = match_range(num_ood, range(1, 4), lambda n: parse_whir_commitment_const(fs, n))
    return fs, root, ood_points, ood_evals


def parse_whir_commitment_const(fs: Mut, num_ood: Const):
    fs, root = fs_receive_chunks(fs, 1)
    fs, ood_points = fs_sample_many_ef(fs, num_ood)
    fs, ood_evals = fs_receive_ef_inlined(fs, num_ood)
    return fs, root, ood_points, ood_evals

@inline
def get_whir_params(n_vars, log_inv_rate):
    debug_assert(WHIR_INITIAL_FOLDING_FACTOR < n_vars)
    nv_except_first_round = n_vars - WHIR_INITIAL_FOLDING_FACTOR
    debug_assert(MAX_NUM_VARIABLES_TO_SEND_COEFFS < nv_except_first_round)
    n_rounds = div_ceil_dynamic(nv_except_first_round - MAX_NUM_VARIABLES_TO_SEND_COEFFS, WHIR_SUBSEQUENT_FOLDING_FACTOR)
    final_vars = nv_except_first_round - n_rounds * WHIR_SUBSEQUENT_FOLDING_FACTOR

    debug_assert(MIN_WHIR_LOG_INV_RATE <= log_inv_rate)
    debug_assert(log_inv_rate <= MAX_WHIR_LOG_INV_RATE)
    num_queries: Imu
    num_queries = get_num_queries(log_inv_rate, n_vars)

    query_grinding_bits: Imu
    query_grinding_bits = get_query_grinding_bits(log_inv_rate, n_vars)

    num_oods = get_num_oods(log_inv_rate, n_vars)

    folding_grinding: Imu
    folding_grinding = get_folding_grinding(log_inv_rate, n_vars)

    return n_rounds, final_vars, num_queries, num_oods, query_grinding_bits, folding_grinding

@inline
def get_num_queries(log_inv_rate, n_vars):
    res = match_range(log_inv_rate, range(MIN_WHIR_LOG_INV_RATE, MAX_WHIR_LOG_INV_RATE + 1), lambda r: get_num_queries_const_rate(r, n_vars))
    return res

def get_num_queries_const_rate(log_inv_rate: Const, n_vars):
    res = match_range(n_vars, range(MIN_STACKED_N_VARS, TWO_ADICITY + WHIR_INITIAL_FOLDING_FACTOR - log_inv_rate + 1), lambda nv: get_num_queries_const(log_inv_rate, nv))
    return res

def get_num_queries_const(log_inv_rate: Const, n_vars: Const):
    max = len(WHIR_ALL_POTENTIAL_NUM_QUERIES[log_inv_rate - MIN_WHIR_LOG_INV_RATE][n_vars - MIN_STACKED_N_VARS])
    num_queries = Array(max)
    for i in unroll(0, max):
        num_queries[i] = WHIR_ALL_POTENTIAL_NUM_QUERIES[log_inv_rate - MIN_WHIR_LOG_INV_RATE][n_vars - MIN_STACKED_N_VARS][i]
    return num_queries


@inline
def get_query_grinding_bits(log_inv_rate, n_vars):
    res = match_range(log_inv_rate, range(MIN_WHIR_LOG_INV_RATE, MAX_WHIR_LOG_INV_RATE + 1), lambda r: get_query_grinding_bits_const_rate(r, n_vars))
    return res

def get_query_grinding_bits_const_rate(log_inv_rate: Const, n_vars):
    res = match_range(n_vars, range(MIN_STACKED_N_VARS, TWO_ADICITY + WHIR_INITIAL_FOLDING_FACTOR - log_inv_rate + 1), lambda nv: get_query_grinding_bits_const(log_inv_rate, nv))
    return res

def get_query_grinding_bits_const(log_inv_rate: Const, n_vars: Const):
    max = len(WHIR_ALL_POTENTIAL_QUERY_GRINDING[log_inv_rate - MIN_WHIR_LOG_INV_RATE][n_vars - MIN_STACKED_N_VARS])
    query_grinding_bits = Array(max)
    for i in unroll(0, max):
        query_grinding_bits[i] = WHIR_ALL_POTENTIAL_QUERY_GRINDING[log_inv_rate - MIN_WHIR_LOG_INV_RATE][n_vars - MIN_STACKED_N_VARS][i]
    return query_grinding_bits

@inline
def get_folding_grinding(log_inv_rate, n_vars):
    res = match_range(log_inv_rate, range(MIN_WHIR_LOG_INV_RATE, MAX_WHIR_LOG_INV_RATE + 1), lambda r: get_folding_grinding_const_rate(r, n_vars))
    return res

def get_folding_grinding_const_rate(log_inv_rate: Const, n_vars):
    res = match_range(n_vars, range(MIN_STACKED_N_VARS, TWO_ADICITY + WHIR_INITIAL_FOLDING_FACTOR - log_inv_rate + 1), lambda nv: get_folding_grinding_const(log_inv_rate, nv))
    return res

def get_folding_grinding_const(log_inv_rate: Const, n_vars: Const):
    max = len(WHIR_ALL_POTENTIAL_FOLDING_GRINDING[log_inv_rate - MIN_WHIR_LOG_INV_RATE][n_vars - MIN_STACKED_N_VARS])
    folding_grinding = Array(max)
    for i in unroll(0, max):
        folding_grinding[i] = WHIR_ALL_POTENTIAL_FOLDING_GRINDING[log_inv_rate - MIN_WHIR_LOG_INV_RATE][n_vars - MIN_STACKED_N_VARS][i]
    return folding_grinding

def get_num_oods(log_inv_rate, n_vars):
    res = match_range(log_inv_rate, range(MIN_WHIR_LOG_INV_RATE, MAX_WHIR_LOG_INV_RATE + 1), lambda r: get_num_oods_const_rate(r, n_vars))
    return res

def get_num_oods_const_rate(log_inv_rate: Const, n_vars):
    res = match_range(n_vars, range(MIN_STACKED_N_VARS, TWO_ADICITY + WHIR_INITIAL_FOLDING_FACTOR - log_inv_rate + 1), lambda nv: get_num_oods_const(log_inv_rate, nv))
    return res


def get_num_oods_const(log_inv_rate: Const, n_vars: Const):
    max = len(WHIR_ALL_POTENTIAL_NUM_OODS[log_inv_rate - MIN_WHIR_LOG_INV_RATE][n_vars - MIN_STACKED_N_VARS])
    num_oods = Array(max)
    for i in unroll(0, max):
        num_oods[i] = WHIR_ALL_POTENTIAL_NUM_OODS[log_inv_rate - MIN_WHIR_LOG_INV_RATE][n_vars - MIN_STACKED_N_VARS][i]
    return num_oods