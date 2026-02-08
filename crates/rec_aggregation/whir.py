from snark_lib import *
from fiat_shamir import *

WHIR_INITIAL_FOLDING_FACTOR = WHIR_INITIAL_FOLDING_FACTOR_PLACEHOLDER
WHIR_SUBSEQUENT_FOLDING_FACTOR = WHIR_SUBSEQUENT_FOLDING_FACTOR_PLACEHOLDER
WHIR_FIRST_RS_REDUCTION_FACTOR = WHIR_FIRST_RS_REDUCTION_FACTOR_PLACEHOLDER
MIN_WHIR_LOG_INV_RATE = MIN_WHIR_LOG_INV_RATE_PLACEHOLDER
MAX_WHIR_LOG_INV_RATE = MAX_WHIR_LOG_INV_RATE_PLACEHOLDER
MAX_NUM_VARIABLES_TO_SEND_COEFFS = MAX_NUM_VARIABLES_TO_SEND_COEFFS_PLACEHOLDER

WHIR_ALL_POTENTIAL_NUM_QUERIES = WHIR_ALL_POTENTIAL_NUM_QUERIES_PLACEHOLDER
WHIR_ALL_POTENTIAL_GRINDING = WHIR_ALL_POTENTIAL_GRINDING_PLACEHOLDER
WHIR_ALL_POTENTIAL_NUM_OODS = WHIR_ALL_POTENTIAL_NUM_OODS_PLACEHOLDER
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
    n_rounds, n_final_vars, num_queries, num_oods, grinding_bits = get_whir_params(n_vars, initial_log_inv_rate)
    n_final_coeffs = powers_of_two(n_final_vars)
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
            grinding_bits[r],
            num_oods[r + 1],
        )
        if r == 0:
            domain_sz -= WHIR_FIRST_RS_REDUCTION_FACTOR
        else:
            domain_sz -= 1

    fs, all_folding_randomness[n_rounds], claimed_sum = sumcheck_verify(
        fs, WHIR_SUBSEQUENT_FOLDING_FACTOR, claimed_sum, 2
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
        grinding_bits[n_rounds],
    )

    final_circle_values = all_circle_values[n_rounds]
    for i in range(0, num_queries[n_rounds]):
        powers_of_2_rev = expand_from_univariate_base(final_circle_values[i], n_final_vars)
        poly_eq = match_range(n_final_vars, range(MAX_NUM_VARIABLES_TO_SEND_COEFFS - WHIR_SUBSEQUENT_FOLDING_FACTOR, MAX_NUM_VARIABLES_TO_SEND_COEFFS + 1), lambda n: poly_eq_base(powers_of_2_rev, n))
        final_pol_evaluated_on_circle = Array(DIM)
        dot_product_be_dynamic(
            poly_eq,
            final_coeffcients,
            final_pol_evaluated_on_circle,
            n_final_coeffs,
        )
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
    poly_eq_final = poly_eq_extension_dynamic(all_folding_randomness[n_rounds + 1], n_final_vars)
    final_value = Array(DIM)
    dot_product_ee_dynamic(poly_eq_final, final_coeffcients, final_value, n_final_coeffs)
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


def sample_stir_indexes_and_fold(
    fs: Mut,
    num_queries,
    merkle_leaves_in_basefield,
    folding_factor,
    two_pow_folding_factor,
    domain_size,
    prev_root,
    folding_randomness,
    grinding_bits,
):
    folded_domain_size = domain_size - folding_factor

    fs = fs_grinding(fs, grinding_bits)
    fs, stir_challenges_indexes = sample_bits_dynamic(fs, num_queries)

    answers = Array(
        num_queries
    )  # a vector of pointers, each pointing to `two_pow_folding_factor` field elements (base if first rounds, extension otherwise)

    n_chunks_per_answer: Imu
    # the number of chunk of 8 field elements per merkle leaf opened
    if merkle_leaves_in_basefield == 1:
        n_chunks_per_answer = two_pow_folding_factor
    else:
        n_chunks_per_answer = two_pow_folding_factor * DIM

    for i in range(0, num_queries):
        fs, answer = fs_hint(fs, n_chunks_per_answer)
        answers[i] = answer

    leaf_hashes = Array(num_queries)  # a vector of vectorized pointers, each pointing to 1 chunk of 8 field elements
    batch_hash_slice(num_queries, answers, leaf_hashes, n_chunks_per_answer / DIGEST_LEN)

    fs, merkle_paths = fs_hint(fs, folded_domain_size * num_queries * DIGEST_LEN)

    # Merkle verification
    merkle_verif_batch(
        merkle_paths,
        leaf_hashes,
        stir_challenges_indexes,
        prev_root,
        folded_domain_size,
        num_queries,
    )

    folds = Array(num_queries * DIM)

    poly_eq = poly_eq_extension_dynamic(folding_randomness, folding_factor)

    if merkle_leaves_in_basefield == 1:
        for i in range(0, num_queries):
            dot_product_be_dynamic(answers[i], poly_eq, folds + i * DIM, two_pow_folding_factor)
    else:
        for i in range(0, num_queries):
            dot_product_ee_dynamic(answers[i], poly_eq, folds + i * DIM, two_pow_folding_factor)

    circle_values = Array(num_queries)  # ROOT^each_stir_index
    for i in range(0, num_queries):
        stir_index_bits = stir_challenges_indexes[i]
        circle_value = unit_root_pow_dynamic(folded_domain_size, stir_index_bits)
        circle_values[i] = circle_value

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
    grinding_bits,
    num_ood,
):
    fs, folding_randomness, new_claimed_sum_a = sumcheck_verify(fs, folding_factor, claimed_sum, 2)

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
        grinding_bits,
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


def polynomial_sum_at_0_and_1(coeffs, degree: Const):
    debug_assert(1 < degree)

    res = Array(DIM * (1 + degree))
    add_extension(coeffs, coeffs, res)  # constant coefficient is doubled
    for i in unroll(0, degree):
        add_extension(res + i * DIM, coeffs + (i + 1) * DIM, res + (i + 1) * DIM)  # TODO use the dot_product precompile
    return res + degree * DIM


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
    num_queries = match_range(log_inv_rate, range(MIN_WHIR_LOG_INV_RATE, MAX_WHIR_LOG_INV_RATE + 1), lambda r: get_num_queries(r))

    grinding_bits: Imu
    grinding_bits = match_range(log_inv_rate, range(MIN_WHIR_LOG_INV_RATE, MAX_WHIR_LOG_INV_RATE + 1), lambda r: get_grinding_bits(r))

    num_oods = get_num_oods(log_inv_rate, n_vars)

    return n_rounds, final_vars, num_queries, num_oods, grinding_bits

def get_num_queries(log_inv_rate: Const):
    max = len(WHIR_ALL_POTENTIAL_NUM_QUERIES[log_inv_rate - MIN_WHIR_LOG_INV_RATE])
    num_queries = Array(max)
    for i in unroll(0, max):
        num_queries[i] = WHIR_ALL_POTENTIAL_NUM_QUERIES[log_inv_rate - MIN_WHIR_LOG_INV_RATE][i]
    return num_queries


def get_grinding_bits(log_inv_rate: Const):
    max = len(WHIR_ALL_POTENTIAL_GRINDING[log_inv_rate - MIN_WHIR_LOG_INV_RATE])
    grinding_bits = Array(max)
    for i in unroll(0, max):
        grinding_bits[i] = WHIR_ALL_POTENTIAL_GRINDING[log_inv_rate - MIN_WHIR_LOG_INV_RATE][i]
    return grinding_bits

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