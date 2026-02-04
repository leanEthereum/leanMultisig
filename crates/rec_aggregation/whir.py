from snark_lib import *
from fiat_shamir import *

N_VARS_BASE = N_VARS_BASE_PLACEHOLDER
LOG_INV_RATE_BASE = LOG_INV_RATE_BASE_PLACEHOLDER
FOLDING_FACTORS_BASE = FOLDING_FACTORS_BASE_PLACEHOLDER
FINAL_VARS_BASE = FINAL_VARS_BASE_PLACEHOLDER
FIRST_RS_REDUCTION_FACTOR_BASE = FIRST_RS_REDUCTION_FACTOR_BASE_PLACEHOLDER
NUM_OOD_COMMIT_BASE = NUM_OOD_COMMIT_BASE_PLACEHOLDER
NUM_OODS_BASE = NUM_OODS_BASE_PLACEHOLDER
GRINDING_BITS_BASE = GRINDING_BITS_BASE_PLACEHOLDER

N_VARS_EXT = N_VARS_EXT_PLACEHOLDER
LOG_INV_RATE_EXT = LOG_INV_RATE_EXT_PLACEHOLDER
FOLDING_FACTORS_EXT = FOLDING_FACTORS_EXT_PLACEHOLDER
FINAL_VARS_EXT = FINAL_VARS_EXT_PLACEHOLDER
FIRST_RS_REDUCTION_FACTOR_EXT = FIRST_RS_REDUCTION_FACTOR_EXT_PLACEHOLDER
NUM_OOD_COMMIT_EXT = NUM_OOD_COMMIT_EXT_PLACEHOLDER
NUM_OODS_EXT = NUM_OODS_EXT_PLACEHOLDER
GRINDING_BITS_EXT = GRINDING_BITS_EXT_PLACEHOLDER


def whir_open_base(
    fs: Mut,
    root: Mut,
    ood_points_commit,
    combination_randomness_powers_0,
    claimed_sum: Mut,
):
    all_folding_randomness = Array(N_ROUNDS_BASE + 2)
    all_ood_points = Array(N_ROUNDS_BASE)
    all_circle_values = Array(N_ROUNDS_BASE + 1)
    all_combination_randomness_powers = Array(N_ROUNDS_BASE)

    domain_sz: Mut = N_VARS_BASE + LOG_INV_RATE_BASE
    for r in unroll(0, N_ROUNDS_BASE):
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
            FOLDING_FACTORS_BASE[r],
            2 ** FOLDING_FACTORS_BASE[r],
            is_first_round,
            NUM_QUERIES_BASE[r],
            domain_sz,
            claimed_sum,
            GRINDING_BITS_BASE[r],
            NUM_OODS_BASE[r],
        )
        if r == 0:
            domain_sz -= FIRST_RS_REDUCTION_FACTOR_BASE
        else:
            domain_sz -= 1

    fs, all_folding_randomness[N_ROUNDS_BASE], claimed_sum = sumcheck_verify(
        fs, FOLDING_FACTORS_BASE[N_ROUNDS_BASE], claimed_sum, 2
    )

    fs, final_coeffcients = fs_receive_ef(fs, 2**FINAL_VARS_BASE)

    fs, all_circle_values[N_ROUNDS_BASE], final_folds = sample_stir_indexes_and_fold(
        fs,
        NUM_QUERIES_BASE[N_ROUNDS_BASE],
        0,
        FOLDING_FACTORS_BASE[N_ROUNDS_BASE],
        2 ** FOLDING_FACTORS_BASE[N_ROUNDS_BASE],
        domain_sz,
        root,
        all_folding_randomness[N_ROUNDS_BASE],
        GRINDING_BITS_BASE[N_ROUNDS_BASE],
    )

    final_circle_values = all_circle_values[N_ROUNDS_BASE]
    for i in range(0, NUM_QUERIES_BASE[N_ROUNDS_BASE]):
        powers_of_2_rev = expand_from_univariate_base_const(final_circle_values[i], FINAL_VARS_BASE)
        poly_eq = poly_eq_base(powers_of_2_rev, FINAL_VARS_BASE)
        final_pol_evaluated_on_circle = Array(DIM)
        dot_product(
            poly_eq,
            final_coeffcients,
            final_pol_evaluated_on_circle,
            2**FINAL_VARS_BASE,
            BE,
        )
        copy_5(final_pol_evaluated_on_circle, final_folds + i * DIM)

    fs, all_folding_randomness[N_ROUNDS_BASE + 1], end_sum = sumcheck_verify(fs, FINAL_VARS_BASE, claimed_sum, 2)

    folding_randomness_global = Array(N_VARS_BASE * DIM)

    start: Mut = folding_randomness_global
    for i in unroll(0, N_ROUNDS_BASE + 1):
        for j in unroll(0, FOLDING_FACTORS_BASE[i]):
            copy_5(all_folding_randomness[i] + j * DIM, start + j * DIM)
        start += FOLDING_FACTORS_BASE[i] * DIM
    for j in unroll(0, FINAL_VARS_BASE):
        copy_5(all_folding_randomness[N_ROUNDS_BASE + 1] + j * DIM, start + j * DIM)

    all_ood_recovered_evals = Array(NUM_OOD_COMMIT_BASE * DIM)
    for i in unroll(0, NUM_OOD_COMMIT_BASE):
        expanded_from_univariate = expand_from_univariate_ext(ood_points_commit + i * DIM, N_VARS_BASE)
        ood_rec = eq_mle_extension(expanded_from_univariate, folding_randomness_global, N_VARS_BASE)
        copy_5(ood_rec, all_ood_recovered_evals + i * DIM)
    s: Mut = dot_product_ret(
        all_ood_recovered_evals,
        combination_randomness_powers_0,
        NUM_OOD_COMMIT_BASE,
        EE,
    )

    n_vars: Mut = N_VARS_BASE
    my_folding_randomness: Mut = folding_randomness_global
    for i in unroll(0, N_ROUNDS_BASE):
        n_vars -= FOLDING_FACTORS_BASE[i]
        my_ood_recovered_evals = Array(NUM_OODS_BASE[i] * DIM)
        combination_randomness_powers = all_combination_randomness_powers[i]
        my_folding_randomness += FOLDING_FACTORS_BASE[i] * DIM
        for j in unroll(0, NUM_OODS_BASE[i]):
            expanded_from_univariate = expand_from_univariate_ext(all_ood_points[i] + j * DIM, n_vars)
            ood_rec = eq_mle_extension(expanded_from_univariate, my_folding_randomness, n_vars)
            copy_5(ood_rec, my_ood_recovered_evals + j * DIM)
        summed_ood = Array(DIM)
        dot_product_ee_dynamic(
            my_ood_recovered_evals,
            combination_randomness_powers,
            summed_ood,
            NUM_OODS_BASE[i],
        )

        s6s = Array((NUM_QUERIES_BASE[i]) * DIM)
        circle_value_i = all_circle_values[i]
        for j in range(0, NUM_QUERIES_BASE[i]):  # unroll ?
            expanded_from_univariate = expand_from_univariate_base(circle_value_i[j], n_vars)
            temp = eq_mle_base_extension(expanded_from_univariate, my_folding_randomness, n_vars)
            copy_5(temp, s6s + j * DIM)
        s7 = dot_product_ret(
            s6s,
            combination_randomness_powers + NUM_OODS_BASE[i] * DIM,
            NUM_QUERIES_BASE[i],
            EE,
        )
        s = add_extension_ret(s, s7)
        s = add_extension_ret(summed_ood, s)
    poly_eq_final = poly_eq_extension(all_folding_randomness[N_ROUNDS_BASE + 1], FINAL_VARS_BASE)
    final_value = dot_product_ret(poly_eq_final, final_coeffcients, 2**FINAL_VARS_BASE, EE)
    # copy_5(mul_extension_ret(s, final_value), end_sum);

    return fs, folding_randomness_global, s, final_value, end_sum


def whir_open_ext(
    fs: Mut,
    root: Mut,
    ood_points_commit,
    combination_randomness_powers_0,
    claimed_sum: Mut,
):
    all_folding_randomness = Array(N_ROUNDS_EXT + 2)
    all_ood_points = Array(N_ROUNDS_EXT)
    all_circle_values = Array(N_ROUNDS_EXT + 1)
    all_combination_randomness_powers = Array(N_ROUNDS_EXT)

    domain_sz: Mut = N_VARS_EXT + LOG_INV_RATE_EXT
    for r in unroll(0, N_ROUNDS_EXT):
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
            FOLDING_FACTORS_EXT[r],
            2 ** FOLDING_FACTORS_EXT[r],
            0,
            NUM_QUERIES_EXT[r],
            domain_sz,
            claimed_sum,
            GRINDING_BITS_EXT[r],
            NUM_OODS_EXT[r],
        )
        if r == 0:
            domain_sz -= FIRST_RS_REDUCTION_FACTOR_EXT
        else:
            domain_sz -= 1

    fs, all_folding_randomness[N_ROUNDS_EXT], claimed_sum = sumcheck_verify(
        fs, FOLDING_FACTORS_EXT[N_ROUNDS_EXT], claimed_sum, 2
    )

    fs, final_coeffcients = fs_receive_ef(fs, 2**FINAL_VARS_EXT)

    fs, all_circle_values[N_ROUNDS_EXT], final_folds = sample_stir_indexes_and_fold(
        fs,
        NUM_QUERIES_EXT[N_ROUNDS_EXT],
        0,
        FOLDING_FACTORS_EXT[N_ROUNDS_EXT],
        2 ** FOLDING_FACTORS_EXT[N_ROUNDS_EXT],
        domain_sz,
        root,
        all_folding_randomness[N_ROUNDS_EXT],
        GRINDING_BITS_EXT[N_ROUNDS_EXT],
    )

    final_circle_values = all_circle_values[N_ROUNDS_EXT]
    for i in range(0, NUM_QUERIES_EXT[N_ROUNDS_EXT]):
        powers_of_2_rev = expand_from_univariate_base_const(final_circle_values[i], FINAL_VARS_EXT)
        poly_eq = poly_eq_base(powers_of_2_rev, FINAL_VARS_EXT)
        final_pol_evaluated_on_circle = Array(DIM)
        dot_product(
            poly_eq,
            final_coeffcients,
            final_pol_evaluated_on_circle,
            2**FINAL_VARS_EXT,
            BE,
        )
        copy_5(final_pol_evaluated_on_circle, final_folds + i * DIM)

    fs, all_folding_randomness[N_ROUNDS_EXT + 1], end_sum = sumcheck_verify(fs, FINAL_VARS_EXT, claimed_sum, 2)

    folding_randomness_global = Array(N_VARS_EXT * DIM)

    start: Mut = folding_randomness_global
    for i in unroll(0, N_ROUNDS_EXT + 1):
        for j in unroll(0, FOLDING_FACTORS_EXT[i]):
            copy_5(all_folding_randomness[i] + j * DIM, start + j * DIM)
        start += FOLDING_FACTORS_EXT[i] * DIM
    for j in unroll(0, FINAL_VARS_EXT):
        copy_5(all_folding_randomness[N_ROUNDS_EXT + 1] + j * DIM, start + j * DIM)

    all_ood_recovered_evals = Array(NUM_OOD_COMMIT_EXT * DIM)
    for i in unroll(0, NUM_OOD_COMMIT_EXT):
        expanded_from_univariate = expand_from_univariate_ext(ood_points_commit + i * DIM, N_VARS_EXT)
        ood_rec = eq_mle_extension(expanded_from_univariate, folding_randomness_global, N_VARS_EXT)
        copy_5(ood_rec, all_ood_recovered_evals + i * DIM)
    s: Mut = dot_product_ret(all_ood_recovered_evals, combination_randomness_powers_0, NUM_OOD_COMMIT_EXT, EE)

    n_vars: Mut = N_VARS_EXT
    my_folding_randomness: Mut = folding_randomness_global
    for i in unroll(0, N_ROUNDS_EXT):
        n_vars -= FOLDING_FACTORS_EXT[i]
        my_ood_recovered_evals = Array(NUM_OODS_EXT[i] * DIM)
        combination_randomness_powers = all_combination_randomness_powers[i]
        my_folding_randomness += FOLDING_FACTORS_EXT[i] * DIM
        for j in unroll(0, NUM_OODS_EXT[i]):
            expanded_from_univariate = expand_from_univariate_ext(all_ood_points[i] + j * DIM, n_vars)
            ood_rec = eq_mle_extension(expanded_from_univariate, my_folding_randomness, n_vars)
            copy_5(ood_rec, my_ood_recovered_evals + j * DIM)
        summed_ood = Array(DIM)
        dot_product_ee_dynamic(
            my_ood_recovered_evals,
            combination_randomness_powers,
            summed_ood,
            NUM_OODS_EXT[i],
        )

        s6s = Array((NUM_QUERIES_EXT[i]) * DIM)
        circle_value_i = all_circle_values[i]
        for j in range(0, NUM_QUERIES_EXT[i]):  # unroll ?
            expanded_from_univariate = expand_from_univariate_base(circle_value_i[j], n_vars)
            temp = eq_mle_base_extension(expanded_from_univariate, my_folding_randomness, n_vars)
            copy_5(temp, s6s + j * DIM)
        s7 = dot_product_ret(
            s6s,
            combination_randomness_powers + NUM_OODS_EXT[i] * DIM,
            NUM_QUERIES_EXT[i],
            EE,
        )
        s = add_extension_ret(s, s7)
        s = add_extension_ret(summed_ood, s)
    poly_eq_final = poly_eq_extension(all_folding_randomness[N_ROUNDS_EXT + 1], FINAL_VARS_EXT)
    final_value = dot_product_ret(poly_eq_final, final_coeffcients, 2**FINAL_VARS_EXT, EE)
    # copy_5(mul_extension_ret(s, final_value), end_sum);

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
            dot_product(answers[i], poly_eq, folds + i * DIM, 2 ** FOLDING_FACTORS_BASE[0], BE)
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
    fs, ood_points = fs_sample_many_ef(fs, num_ood)
    fs, ood_evals = fs_receive_ef(fs, num_ood)
    return fs, root, ood_points, ood_evals
