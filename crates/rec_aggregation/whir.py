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

# Specialization for the recursion verifier (single fixed config).
# `whir_open` asserts the runtime values match these and uses the constants for full unrolling.
RECUR_LOG_INV_RATE = RECUR_LOG_INV_RATE_PLACEHOLDER
RECUR_STACKED_N_VARS = RECUR_STACKED_N_VARS_PLACEHOLDER
RECUR_N_ROUNDS = RECUR_N_ROUNDS_PLACEHOLDER
RECUR_N_FINAL_VARS = RECUR_N_FINAL_VARS_PLACEHOLDER
RECUR_NUM_QUERIES = RECUR_NUM_QUERIES_PLACEHOLDER  # length n_rounds + 1
RECUR_QUERY_GRINDING = RECUR_QUERY_GRINDING_PLACEHOLDER
RECUR_NUM_OODS = RECUR_NUM_OODS_PLACEHOLDER  # length n_rounds + 1 (commitment + per-round)
RECUR_FOLDING_GRINDING = RECUR_FOLDING_GRINDING_PLACEHOLDER  # length n_rounds + 1


def whir_open(
    fs: Mut,
    n_vars,
    initial_log_inv_rate,
    root: Mut,
    ood_points_commit,
    combination_randomness_powers_0,
    claimed_sum: Mut,
):
    # Recursion-specialized: the recursion verifier always sees the same WHIR config.
    # The runtime asserts catch shape mismatches; everything below uses compile-time constants.
    assert n_vars == RECUR_STACKED_N_VARS
    assert initial_log_inv_rate == RECUR_LOG_INV_RATE

    all_folding_randomness = Array(RECUR_N_ROUNDS + 2)
    all_ood_points = Array(RECUR_N_ROUNDS)
    all_circle_values = Array(RECUR_N_ROUNDS + 1)
    all_combination_randomness_powers = Array(RECUR_N_ROUNDS)

    # Compile-time domain size at each round (initial - WHIR_FIRST_RS_REDUCTION_FACTOR after r=0,
    # then -1 per subsequent round).
    initial_domain_sz = RECUR_STACKED_N_VARS + RECUR_LOG_INV_RATE

    # Round 0: initial folding factor, basefield merkle leaves.
    (
        fs,
        all_folding_randomness[0],
        all_ood_points[0],
        root,
        all_circle_values[0],
        all_combination_randomness_powers[0],
        claimed_sum,
    ) = whir_round(
        fs,
        root,
        WHIR_INITIAL_FOLDING_FACTOR,
        2 ** WHIR_INITIAL_FOLDING_FACTOR,
        1,
        RECUR_NUM_QUERIES[0],
        initial_domain_sz,
        claimed_sum,
        RECUR_QUERY_GRINDING[0],
        RECUR_NUM_OODS[1],
        RECUR_FOLDING_GRINDING[0],
    )

    # Subsequent rounds (r=1..RECUR_N_ROUNDS-1): subsequent folding factor, ext-field merkle leaves.
    for r in unroll(1, RECUR_N_ROUNDS):
        domain_sz_r = initial_domain_sz - WHIR_FIRST_RS_REDUCTION_FACTOR - (r - 1)
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
            WHIR_SUBSEQUENT_FOLDING_FACTOR,
            2 ** WHIR_SUBSEQUENT_FOLDING_FACTOR,
            0,
            RECUR_NUM_QUERIES[r],
            domain_sz_r,
            claimed_sum,
            RECUR_QUERY_GRINDING[r],
            RECUR_NUM_OODS[r + 1],
            RECUR_FOLDING_GRINDING[r],
        )

    final_domain_sz = initial_domain_sz - WHIR_FIRST_RS_REDUCTION_FACTOR - (RECUR_N_ROUNDS - 1)

    fs, all_folding_randomness[RECUR_N_ROUNDS], claimed_sum = sumcheck_verify_with_grinding_unrolled(
        fs, WHIR_SUBSEQUENT_FOLDING_FACTOR, claimed_sum, 2, RECUR_FOLDING_GRINDING[RECUR_N_ROUNDS]
    )

    fs, final_coeffcients = fs_receive_ef(fs, 2 ** RECUR_N_FINAL_VARS)

    fs, all_circle_values[RECUR_N_ROUNDS], final_folds = sample_stir_indexes_and_fold(
        fs,
        RECUR_NUM_QUERIES[RECUR_N_ROUNDS],
        0,
        WHIR_SUBSEQUENT_FOLDING_FACTOR,
        2 ** WHIR_SUBSEQUENT_FOLDING_FACTOR,
        final_domain_sz,
        root,
        all_folding_randomness[RECUR_N_ROUNDS],
        RECUR_QUERY_GRINDING[RECUR_N_ROUNDS],
    )

    final_circle_values = all_circle_values[RECUR_N_ROUNDS]
    for i in unroll(0, RECUR_NUM_QUERIES[RECUR_N_ROUNDS]):
        alpha = final_circle_values[i]
        final_pol_evaluated_on_circle = univariate_eval_on_base(final_coeffcients, alpha, RECUR_N_FINAL_VARS)
        copy_5(final_pol_evaluated_on_circle, final_folds + i * DIM)

    fs, all_folding_randomness[RECUR_N_ROUNDS + 1], end_sum = sumcheck_verify_unrolled(fs, RECUR_N_FINAL_VARS, claimed_sum, 2)

    folding_randomness_global = Array(RECUR_STACKED_N_VARS * DIM)

    # WHIR sumcheck folds LSB-first: write each chronological challenge to position
    # (n_vars - 1 - chrono_idx) so the final cumulative reads as [x_0, ..., x_{n-1}].
    # Round 0 contributes WHIR_INITIAL_FOLDING_FACTOR challenges, then RECUR_N_ROUNDS - 1
    # rounds contribute WHIR_SUBSEQUENT_FOLDING_FACTOR each, then the final folding sumcheck
    # contributes another WHIR_SUBSEQUENT_FOLDING_FACTOR, then RECUR_N_FINAL_VARS more.
    chrono_idx: Mut = 0
    for j in unroll(0, WHIR_INITIAL_FOLDING_FACTOR):
        copy_5(all_folding_randomness[0] + j * DIM, folding_randomness_global + (RECUR_STACKED_N_VARS - 1 - chrono_idx) * DIM)
        chrono_idx += 1
    for i in unroll(1, RECUR_N_ROUNDS + 1):
        for j in unroll(0, WHIR_SUBSEQUENT_FOLDING_FACTOR):
            copy_5(all_folding_randomness[i] + j * DIM, folding_randomness_global + (RECUR_STACKED_N_VARS - 1 - chrono_idx) * DIM)
            chrono_idx += 1
    for j in unroll(0, RECUR_N_FINAL_VARS):
        copy_5(all_folding_randomness[RECUR_N_ROUNDS + 1] + j * DIM, folding_randomness_global + (RECUR_STACKED_N_VARS - 1 - chrono_idx) * DIM)
        chrono_idx += 1

    all_ood_recovered_evals = Array(RECUR_NUM_OODS[0] * DIM)
    for i in unroll(0, RECUR_NUM_OODS[0]):
        expanded_from_univariate = expand_from_univariate_ext_const(ood_points_commit + i * DIM, RECUR_STACKED_N_VARS)
        poly_eq_ee(expanded_from_univariate, folding_randomness_global, all_ood_recovered_evals + i * DIM, RECUR_STACKED_N_VARS)
    s: Mut = Array(DIM)
    dot_product_ee(all_ood_recovered_evals, combination_randomness_powers_0, s, RECUR_NUM_OODS[0])

    # n_vars_remaining at round i (compile-time): RECUR_STACKED_N_VARS - WHIR_INITIAL_FOLDING_FACTOR - i * WHIR_SUBSEQUENT_FOLDING_FACTOR.
    # (Round 0 subtracts WHIR_INITIAL_FOLDING_FACTOR; the i*WHIR_SUBSEQUENT_FOLDING_FACTOR term is 0 then.)
    for i in unroll(0, RECUR_N_ROUNDS):
        n_vars_remaining_const = RECUR_STACKED_N_VARS - WHIR_INITIAL_FOLDING_FACTOR - i * WHIR_SUBSEQUENT_FOLDING_FACTOR
        my_ood_recovered_evals = Array(RECUR_NUM_OODS[i + 1] * DIM)
        combination_randomness_powers = all_combination_randomness_powers[i]
        for j in unroll(0, RECUR_NUM_OODS[i + 1]):
            expanded_from_univariate = expand_from_univariate_ext_const(all_ood_points[i] + j * DIM, n_vars_remaining_const)
            poly_eq_ee(expanded_from_univariate, folding_randomness_global, my_ood_recovered_evals + j * DIM, n_vars_remaining_const)
        summed_ood = Array(DIM)
        dot_product_ee(my_ood_recovered_evals, combination_randomness_powers, summed_ood, RECUR_NUM_OODS[i + 1])

        s6s = Array(RECUR_NUM_QUERIES[i] * DIM)
        circle_value_i = all_circle_values[i]
        for j in unroll(0, RECUR_NUM_QUERIES[i]):
            expanded_from_univariate = expand_from_univariate_base_const(circle_value_i[j], n_vars_remaining_const)
            poly_eq_be(expanded_from_univariate, folding_randomness_global, s6s + j * DIM, n_vars_remaining_const)
        s7 = Array(DIM)
        dot_product_ee(s6s, combination_randomness_powers + RECUR_NUM_OODS[i + 1] * DIM, s7, RECUR_NUM_QUERIES[i])
        s = add_extension_ret(s, s7)
        s = add_extension_ret(summed_ood, s)

    # WHIR sumcheck folds LSB-first: final_sumcheck challenges are [r_1=x_{m-1}, ..., r_m=x_0].
    # eval_multilinear_coeffs_rev computes f(x_j = point[j]); reverse first.
    final_sumcheck_chals_rev = Array(RECUR_N_FINAL_VARS * DIM)
    final_sumcheck_chals = all_folding_randomness[RECUR_N_ROUNDS + 1]
    for j in unroll(0, RECUR_N_FINAL_VARS):
        copy_5(final_sumcheck_chals + (RECUR_N_FINAL_VARS - 1 - j) * DIM, final_sumcheck_chals_rev + j * DIM)
    final_value = eval_multilinear_coeffs_rev(final_coeffcients, final_sumcheck_chals_rev, RECUR_N_FINAL_VARS)

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


def sumcheck_verify_reversed(fs: Mut, n_steps, claimed_sum: Mut, degree: Const):
    challenges = Array(n_steps * DIM)
    fs, new_claimed_sum = sumcheck_verify_reversed_helper(fs, n_steps, claimed_sum, degree, challenges)
    return fs, challenges, new_claimed_sum


def sumcheck_verify_reversed_helper(fs: Mut, n_steps, claimed_sum: Mut, degree: Const, challenges):
    for sc_round in range(0, n_steps):
        fs, poly = fs_receive_ef_inlined(fs, degree + 1)
        sum_over_boolean_hypercube = polynomial_sum_at_0_and_1(poly, degree)
        copy_5(sum_over_boolean_hypercube, claimed_sum)
        fs, rand = fs_sample_ef(fs)
        claimed_sum = univariate_polynomial_eval(poly, rand, degree)
        copy_5(rand, challenges + (n_steps - 1 - sc_round) * DIM)

    return fs, claimed_sum


# `@inline`-able variant of sumcheck_verify_reversed_helper (no Mut params).
# Use this when the caller can pass `n_steps` as a compile-time constant so the
# inner loop fully unrolls (e.g. inside an `unroll`ed GKR step loop).
@inline
def sumcheck_verify_reversed_helper_unrolled(start_fs, n_steps, start_claimed_sum, degree, challenges):
    fs: Mut = start_fs
    claimed_sum: Mut = start_claimed_sum
    for sc_round in unroll(0, n_steps):
        fs, poly = fs_receive_ef_inlined(fs, degree + 1)
        sum_over_boolean_hypercube = polynomial_sum_at_0_and_1(poly, degree)
        copy_5(sum_over_boolean_hypercube, claimed_sum)
        fs, rand = fs_sample_ef(fs)
        claimed_sum = univariate_polynomial_eval(poly, rand, degree)
        copy_5(rand, challenges + (n_steps - 1 - sc_round) * DIM)

    return fs, claimed_sum


# `@inline`-able variant of sumcheck_verify_reversed (no Mut params, fully unrolled).
@inline
def sumcheck_verify_reversed_unrolled(start_fs, n_steps, start_claimed_sum, degree):
    fs: Mut = start_fs
    challenges = Array(n_steps * DIM)
    fs, new_claimed_sum = sumcheck_verify_reversed_helper_unrolled(fs, n_steps, start_claimed_sum, degree, challenges)
    return fs, challenges, new_claimed_sum


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


# `@inline`-able variant: caller must pass a compile-time-known `n_steps`
# (e.g. via literal arg or `unroll`) so the inner loop fully unrolls.
@inline
def sumcheck_verify_with_grinding_unrolled(start_fs, n_steps, start_claimed_sum, degree, folding_grinding_bits):
    fs: Mut = start_fs
    claimed_sum: Mut = start_claimed_sum
    challenges = Array(n_steps * DIM)
    for sc_round in unroll(0, n_steps):
        fs, poly = fs_receive_ef_inlined(fs, degree + 1)
        sum_over_boolean_hypercube = polynomial_sum_at_0_and_1(poly, degree)
        copy_5(sum_over_boolean_hypercube, claimed_sum)
        fs = fs_grinding(fs, folding_grinding_bits)
        fs, rand = fs_sample_ef(fs)
        claimed_sum = univariate_polynomial_eval(poly, rand, degree)
        copy_5(rand, challenges + sc_round * DIM)

    return fs, challenges, claimed_sum


@inline
def sumcheck_verify_unrolled(start_fs, n_steps, start_claimed_sum, degree):
    fs: Mut = start_fs
    challenges = Array(n_steps * DIM)
    claimed_sum: Mut = start_claimed_sum
    for sc_round in unroll(0, n_steps):
        fs, poly = fs_receive_ef_inlined(fs, degree + 1)
        sum_over_boolean_hypercube = polynomial_sum_at_0_and_1(poly, degree)
        copy_5(sum_over_boolean_hypercube, claimed_sum)
        fs, rand = fs_sample_ef(fs)
        claimed_sum = univariate_polynomial_eval(poly, rand, degree)
        copy_5(rand, challenges + sc_round * DIM)
    return fs, challenges, claimed_sum


@inline
def decompose_and_verify_merkle_batch(num_queries, sampled, root, height, num_chunks, circle_values, answers):
    debug_assert(height < 25)
    match_range(
        height,
        range(5, 25),
        lambda h: decompose_and_verify_merkle_batch_with_height(num_queries, sampled, root, h, num_chunks, circle_values, answers),
    )
    return


# Const variant: caller passes both height and num_chunks as compile-time constants
# (e.g. recursion verifier where the WHIR domain size and folding factor are known).
def decompose_and_verify_merkle_batch_full_const(num_queries, sampled, root, height: Const, num_chunks: Const, circle_values, answers):
    decompose_and_verify_merkle_batch_const(num_queries, sampled, root, height, num_chunks, circle_values, answers)
    return


def decompose_and_verify_merkle_batch_with_height(num_queries, sampled, root, height: Const, num_chunks, circle_values, answers):
    if num_chunks == DIM * 2:
        decompose_and_verify_merkle_batch_const(num_queries, sampled, root, height, DIM * 2, circle_values, answers)
        return
    if num_chunks == 16:
        decompose_and_verify_merkle_batch_const(num_queries, sampled, root, height, 16, circle_values, answers)
        return
    if num_chunks == 8:
        decompose_and_verify_merkle_batch_const(num_queries, sampled, root, height, 8, circle_values, answers)
        return
    if num_chunks == 20:
        decompose_and_verify_merkle_batch_const(num_queries, sampled, root, height, 20, circle_values, answers)
        return
    if num_chunks == 1:
        decompose_and_verify_merkle_batch_const(num_queries, sampled, root, height, 1, circle_values, answers)
        return
    if num_chunks == 4:
        decompose_and_verify_merkle_batch_const(num_queries, sampled, root, height, 4, circle_values, answers)
        return
    if num_chunks == 5:
        decompose_and_verify_merkle_batch_const(num_queries, sampled, root, height, 5, circle_values, answers)
        return
    print(num_chunks)
    assert False, "decompose_and_verify_merkle_batch called with unsupported num_chunks"


def decompose_and_verify_merkle_batch_const(num_queries, sampled, root, height: Const, num_chunks: Const, circle_values, merkle_leaves):
    for i in range(0, num_queries):
        merkle_leaves[i], circle_values[i] = decompose_and_verify_merkle_query(sampled[i], height, root, num_chunks)
    return


@inline
def sample_stir_indexes_and_fold(
    start_fs,
    num_queries,
    merkle_leaves_in_basefield,
    folding_factor,
    two_pow_folding_factor,
    domain_size,
    prev_root,
    folding_randomness,
    query_grinding_bits,
):
    fs: Mut = start_fs
    # Caller passes compile-time-constant num_queries / folding_factor / two_pow_folding_factor
    # / merkle_leaves_in_basefield / domain_size (recursion verifier specialization).
    folded_domain_size = domain_size - folding_factor

    fs = fs_grinding(fs, query_grinding_bits)
    sampled, fs = fs_sample_queries_const(fs, num_queries)

    merkle_leaves = Array(num_queries)
    circle_values = Array(num_queries)

    # All inputs are compile-time constants in the recursion-specialized path; compute
    # n_chunks at compile time and dispatch directly into the const merkle verifier.
    if merkle_leaves_in_basefield == 1:
        decompose_and_verify_merkle_batch_full_const(
            num_queries,
            sampled,
            prev_root,
            folded_domain_size,
            two_pow_folding_factor / DIGEST_LEN,
            circle_values,
            merkle_leaves,
        )
    else:
        decompose_and_verify_merkle_batch_full_const(
            num_queries,
            sampled,
            prev_root,
            folded_domain_size,
            two_pow_folding_factor * DIM / DIGEST_LEN,
            circle_values,
            merkle_leaves,
        )

    folds = Array(num_queries * DIM)

    # WHIR sumcheck folds LSB-first; the leaf is laid out so its first var is the polynomial's
    # last LSB-folded var. evaluate (poly_eq) is MSB-first, so reverse the per-round challenges.
    folding_randomness_reversed = Array(folding_factor * DIM)
    for j in unroll(0, folding_factor):
        copy_5(folding_randomness + (folding_factor - 1 - j) * DIM, folding_randomness_reversed + j * DIM)
    poly_eq = poly_eq_extension(folding_randomness_reversed, folding_factor)

    if merkle_leaves_in_basefield == 1:
        for i in unroll(0, num_queries):
            dot_product_be(merkle_leaves[i], poly_eq, folds + i * DIM, two_pow_folding_factor)
    else:
        for i in unroll(0, num_queries):
            dot_product_ee(merkle_leaves[i], poly_eq, folds + i * DIM, two_pow_folding_factor)

    return fs, circle_values, folds


@inline
def whir_round(
    start_fs,
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
    fs: Mut = start_fs
    # Caller passes compile-time constants for folding_factor, num_queries, num_ood, etc.,
    # so we can use the fully-unrolled helpers and skip runtime match_range dispatches.
    fs, folding_randomness, new_claimed_sum_a = sumcheck_verify_with_grinding_unrolled(
        fs, folding_factor, claimed_sum, 2, folding_grinding_bits
    )

    fs, root, ood_points, ood_evals = parse_whir_commitment_const(fs, num_ood)

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

    combination_randomness_powers = powers_const(combination_randomness_gen, num_queries + num_ood)

    claimed_sum_0 = Array(DIM)
    dot_product_ee(ood_evals, combination_randomness_powers, claimed_sum_0, num_ood)

    claimed_sum_1 = Array(DIM)
    dot_product_ee(folds, combination_randomness_powers + num_ood * DIM, claimed_sum_1, num_queries)

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


@inline
def parse_commitment(start_fs, num_ood):
    fs: Mut = start_fs
    root: Imu
    ood_points: Imu
    ood_evals: Imu
    debug_assert(num_ood < 5)
    debug_assert(num_ood != 0)
    fs, root, ood_points, ood_evals = match_range(num_ood, range(1, 5), lambda n: parse_whir_commitment_const(fs, n))
    return fs, root, ood_points, ood_evals


def parse_whir_commitment_const(fs: Mut, num_ood: Const):
    fs, root = fs_receive_chunks(fs, 1)
    fs, ood_points = fs_sample_many_ef_const(fs, num_ood)
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
    res = match_range(
        n_vars,
        range(MIN_STACKED_N_VARS, TWO_ADICITY + WHIR_INITIAL_FOLDING_FACTOR - log_inv_rate + 1),
        lambda nv: get_num_queries_const(log_inv_rate, nv),
    )
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
    res = match_range(
        n_vars,
        range(MIN_STACKED_N_VARS, TWO_ADICITY + WHIR_INITIAL_FOLDING_FACTOR - log_inv_rate + 1),
        lambda nv: get_query_grinding_bits_const(log_inv_rate, nv),
    )
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
    res = match_range(
        n_vars,
        range(MIN_STACKED_N_VARS, TWO_ADICITY + WHIR_INITIAL_FOLDING_FACTOR - log_inv_rate + 1),
        lambda nv: get_folding_grinding_const(log_inv_rate, nv),
    )
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
    res = match_range(
        n_vars,
        range(MIN_STACKED_N_VARS, TWO_ADICITY + WHIR_INITIAL_FOLDING_FACTOR - log_inv_rate + 1),
        lambda nv: get_num_oods_const(log_inv_rate, nv),
    )
    return res


def get_num_oods_const(log_inv_rate: Const, n_vars: Const):
    max = len(WHIR_ALL_POTENTIAL_NUM_OODS[log_inv_rate - MIN_WHIR_LOG_INV_RATE][n_vars - MIN_STACKED_N_VARS])
    num_oods = Array(max)
    for i in unroll(0, max):
        num_oods[i] = WHIR_ALL_POTENTIAL_NUM_OODS[log_inv_rate - MIN_WHIR_LOG_INV_RATE][n_vars - MIN_STACKED_N_VARS][i]
    return num_oods
