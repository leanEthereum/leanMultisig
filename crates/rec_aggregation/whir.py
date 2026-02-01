from snark_lib import *
from fiat_shamir import *

WHIR_N_VARS = WHIR_N_VARS_PLACEHOLDER
WHIR_LOG_INV_RATE = WHIR_LOG_INV_RATE_PLACEHOLDER
WHIR_FOLDING_FACTORS = WHIR_FOLDING_FACTORS_PLACEHOLDER
WHIR_FINAL_VARS = WHIR_FINAL_VARS_PLACEHOLDER
WHIR_FIRST_RS_REDUCTION_FACTOR = WHIR_FIRST_RS_REDUCTION_FACTOR_PLACEHOLDER
WHIR_NUM_OOD_COMMIT = WHIR_NUM_OOD_COMMIT_PLACEHOLDER
WHIR_NUM_OODS = WHIR_NUM_OODS_PLACEHOLDER
WHIR_GRINDING_BITS = WHIR_GRINDING_BITS_PLACEHOLDER



def whir_open(
    fs: Mut,
    root: Mut,
    ood_points_commit,
    combination_randomness_powers_0,
    claimed_sum: Mut,
):
    all_folding_randomness = Array(WHIR_N_ROUNDS + 2)
    all_ood_points = Array(WHIR_N_ROUNDS)
    all_circle_values = Array(WHIR_N_ROUNDS + 1)
    all_combination_randomness_powers = Array(WHIR_N_ROUNDS)

    domain_sz: Mut = WHIR_N_VARS + WHIR_LOG_INV_RATE
    for r in unroll(0, WHIR_N_ROUNDS):
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
            WHIR_FOLDING_FACTORS[r],
            2 ** WHIR_FOLDING_FACTORS[r],
            is_first_round,
            NUM_QUERIES[r],
            domain_sz,
            claimed_sum,
            WHIR_GRINDING_BITS[r],
            WHIR_NUM_OODS[r],
        )
        if r == 0:
            domain_sz -= WHIR_FIRST_RS_REDUCTION_FACTOR
        else:
            domain_sz -= 1

    fs, all_folding_randomness[WHIR_N_ROUNDS], claimed_sum = sumcheck_verify(
        fs, WHIR_FOLDING_FACTORS[WHIR_N_ROUNDS], claimed_sum, 2
    )

    fs, final_coeffcients = fs_receive_ef(fs, 2**WHIR_FINAL_VARS)

    fs, all_circle_values[WHIR_N_ROUNDS], final_folds = sample_stir_indexes_and_fold(
        fs,
        NUM_QUERIES[WHIR_N_ROUNDS],
        0,
        WHIR_FOLDING_FACTORS[WHIR_N_ROUNDS],
        2 ** WHIR_FOLDING_FACTORS[WHIR_N_ROUNDS],
        domain_sz,
        root,
        all_folding_randomness[WHIR_N_ROUNDS],
        WHIR_GRINDING_BITS[WHIR_N_ROUNDS],
    )

    final_circle_values = all_circle_values[WHIR_N_ROUNDS]
    for i in range(0, NUM_QUERIES[WHIR_N_ROUNDS]):
        powers_of_2_rev = expand_from_univariate_base_const(final_circle_values[i], WHIR_FINAL_VARS)
        poly_eq = poly_eq_base(powers_of_2_rev, WHIR_FINAL_VARS)
        final_pol_evaluated_on_circle = Array(DIM)
        dot_product(
            poly_eq,
            final_coeffcients,
            final_pol_evaluated_on_circle,
            2**WHIR_FINAL_VARS,
            BE,
        )
        copy_5(final_pol_evaluated_on_circle, final_folds + i * DIM)

    fs, all_folding_randomness[WHIR_N_ROUNDS + 1], end_sum = sumcheck_verify(fs, WHIR_FINAL_VARS, claimed_sum, 2)

    folding_randomness_global = Array(WHIR_N_VARS * DIM)

    start: Mut = folding_randomness_global
    for i in unroll(0, WHIR_N_ROUNDS + 1):
        for j in unroll(0, WHIR_FOLDING_FACTORS[i]):
            copy_5(all_folding_randomness[i] + j * DIM, start + j * DIM)
        start += WHIR_FOLDING_FACTORS[i] * DIM
    for j in unroll(0, WHIR_FINAL_VARS):
        copy_5(all_folding_randomness[WHIR_N_ROUNDS + 1] + j * DIM, start + j * DIM)

    all_ood_recovered_evals = Array(WHIR_NUM_OOD_COMMIT * DIM)
    for i in unroll(0, WHIR_NUM_OOD_COMMIT):
        expanded_from_univariate = expand_from_univariate_ext(ood_points_commit + i * DIM, WHIR_N_VARS)
        ood_rec = eq_mle_extension(expanded_from_univariate, folding_randomness_global, WHIR_N_VARS)
        copy_5(ood_rec, all_ood_recovered_evals + i * DIM)
    s: Mut = dot_product_ret(
        all_ood_recovered_evals,
        combination_randomness_powers_0,
        WHIR_NUM_OOD_COMMIT,
        EE,
    )

    n_vars: Mut = WHIR_N_VARS
    my_folding_randomness: Mut = folding_randomness_global
    for i in unroll(0, WHIR_N_ROUNDS):
        n_vars -= WHIR_FOLDING_FACTORS[i]
        my_ood_recovered_evals = Array(WHIR_NUM_OODS[i] * DIM)
        combination_randomness_powers = all_combination_randomness_powers[i]
        my_folding_randomness += WHIR_FOLDING_FACTORS[i] * DIM
        for j in unroll(0, WHIR_NUM_OODS[i]):
            expanded_from_univariate = expand_from_univariate_ext(all_ood_points[i] + j * DIM, n_vars)
            ood_rec = eq_mle_extension(expanded_from_univariate, my_folding_randomness, n_vars)
            copy_5(ood_rec, my_ood_recovered_evals + j * DIM)
        summed_ood = Array(DIM)
        dot_product_ee_dynamic(
            my_ood_recovered_evals,
            combination_randomness_powers,
            summed_ood,
            WHIR_NUM_OODS[i],
        )

        s6s = Array((NUM_QUERIES[i]) * DIM)
        circle_value_i = all_circle_values[i]
        for j in range(0, NUM_QUERIES[i]):  # unroll ?
            expanded_from_univariate = expand_from_univariate_base(circle_value_i[j], n_vars)
            temp = eq_mle_base_extension(expanded_from_univariate, my_folding_randomness, n_vars)
            copy_5(temp, s6s + j * DIM)
        s7 = dot_product_ret(
            s6s,
            combination_randomness_powers + WHIR_NUM_OODS[i] * DIM,
            NUM_QUERIES[i],
            EE,
        )
        s = add_extension_ret(s, s7)
        s = add_extension_ret(summed_ood, s)
    poly_eq_final = poly_eq_extension(all_folding_randomness[WHIR_N_ROUNDS + 1], WHIR_FINAL_VARS)
    final_value = dot_product_ret(poly_eq_final, final_coeffcients, 2**WHIR_FINAL_VARS, EE)
    # copy_5(mul_extension_ret(s, final_value), end_sum);

    fs = duplexing(fs)

    return fs, folding_randomness_global, s, final_value, end_sum

def sumcheck_verify(fs: Mut, n_steps, claimed_sum, degree: Const):
    challenges = Array(n_steps * DIM)
    fs, new_claimed_sum = sumcheck_verify_helper(fs, n_steps, claimed_sum, degree, challenges)
    return fs, challenges, new_claimed_sum


def sumcheck_verify_helper(fs: Mut, n_steps, claimed_sum: Mut, degree: Const, challenges):
    for sc_round in range(0, n_steps):
        fs, poly = fs_receive_ef(fs, degree + 1)
        sum_over_boolean_hypercube = polynomial_sum_at_0_and_1(poly, degree)
        copy_5(sum_over_boolean_hypercube, claimed_sum)
        rand = fs_sample_ef(fs)
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
    fs, stir_challenges_indexes = sample_bits_dynamic(fs, num_queries, folded_domain_size)

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
    batch_hash_slice(num_queries, answers, leaf_hashes, n_chunks_per_answer / VECTOR_LEN)

    fs, merkle_paths = fs_hint(fs, folded_domain_size * num_queries * VECTOR_LEN)

    # Merkle verification
    merkle_verif_batch(
        num_queries,
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
            dot_product(answers[i], poly_eq, folds + i * DIM, 2 ** WHIR_FOLDING_FACTORS[0], BE)
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

    combination_randomness_gen = fs_sample_ef(fs)

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
    match num_ood:
        case 0:
            _ = 0  # unreachable
        case 1:
            fs, root, ood_points, ood_evals = parse_whir_commitment_const(fs, 1)
        case 2:
            fs, root, ood_points, ood_evals = parse_whir_commitment_const(fs, 2)
        case 3:
            fs, root, ood_points, ood_evals = parse_whir_commitment_const(fs, 3)
        case 4:
            fs, root, ood_points, ood_evals = parse_whir_commitment_const(fs, 4)
    return fs, root, ood_points, ood_evals


def parse_whir_commitment_const(fs: Mut, num_ood: Const):
    fs, root = fs_receive_chunks(fs, 1)
    ood_points = Array(num_ood * DIM)
    for i in unroll(0, num_ood):
        ood_point = fs_sample_ef(fs)
        copy_5(ood_point, ood_points + i * DIM)
        fs = duplexing(fs)
    fs, ood_evals = fs_receive_ef(fs, num_ood)
    return fs, root, ood_points, ood_evals
