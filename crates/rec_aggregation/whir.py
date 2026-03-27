from snark_lib import *
from fiat_shamir import *

WHIR_INITIAL_FOLDING_FACTOR = WHIR_INITIAL_FOLDING_FACTOR_PLACEHOLDER
MIN_WHIR_LOG_INV_RATE = MIN_WHIR_LOG_INV_RATE_PLACEHOLDER
MAX_WHIR_LOG_INV_RATE = MAX_WHIR_LOG_INV_RATE_PLACEHOLDER


def whir_open(
    fs: Mut,
    n_vars,
    initial_log_inv_rate,
    root: Mut,
    ood_points_commit,
    combination_randomness_powers_0,
    claimed_sum: Mut,
):
    # Specialized for n_vars=25, log_inv_rate=2
    # n_rounds=2, n_final_vars=8
    # queries=[113, 55, 27], oods=[2, 1, 2], qgrind=[17, 16, 16], fgrind=[0, 0, 0]
    # folding_factors=[7, 5, 5], domain_sz: 27->22->21
    assert n_vars == 25
    assert initial_log_inv_rate == 2

    all_folding_randomness = Array(4)
    all_ood_points = Array(2)
    all_circle_values = Array(3)
    all_combination_randomness_powers = Array(2)

    # Round 0: fold=7, 2^7=128, first_round=1, queries=113, domain=27, qgrind=17, oods=1, fgrind=0
    (
        fs,
        all_folding_randomness[0],
        all_ood_points[0],
        root,
        all_circle_values[0],
        all_combination_randomness_powers[0],
        claimed_sum,
    ) = whir_round_0(fs, root, claimed_sum)

    # Round 1: fold=5, 2^5=32, first_round=0, queries=55, domain=22, qgrind=16, oods=2, fgrind=0
    (
        fs,
        all_folding_randomness[1],
        all_ood_points[1],
        root,
        all_circle_values[1],
        all_combination_randomness_powers[1],
        claimed_sum,
    ) = whir_round_1(fs, root, claimed_sum)

    # Final folding sumcheck: fold=5, grinding=0
    fs, all_folding_randomness[2], claimed_sum = sumcheck_verify_unrolled(fs, 5, claimed_sum, 2)

    # Receive final coefficients: n_final_vars=8, 2^8=256
    fs, final_coefficients = fs_receive_ef(fs, 256)

    # Final STIR queries: 27 queries, fold=5, 2^5=32, domain=21, qgrind=16
    fs, all_circle_values[2], final_folds = sample_stir_indexes_and_fold_final(fs, root, all_folding_randomness[2])

    # Evaluate final polynomial on circle: n_final_vars=8, 2^8=256
    final_circle_values = all_circle_values[2]
    for i in range(0, 27):
        alpha = final_circle_values[i]
        alpha_powers = Array(256)
        alpha_powers[0] = 1
        for k in unroll(0, 255):
            alpha_powers[k + 1] = alpha_powers[k] * alpha
        dot_product_be(alpha_powers, final_coefficients, final_folds + i * DIM, 256)

    # Final sumcheck: n_final_vars=8
    fs, all_folding_randomness[3], end_sum = sumcheck_verify_unrolled(fs, 8, claimed_sum, 2)

    # Assemble folding_randomness_global: 25 * DIM = 125
    folding_randomness_global = Array(125)
    # Round 0: 7 challenges -> offsets 0..35
    for j in unroll(0, 7):
        copy_5(all_folding_randomness[0] + j * DIM, folding_randomness_global + j * DIM)
    # Round 1: 5 challenges -> offsets 35..60
    for j in unroll(0, 5):
        copy_5(all_folding_randomness[1] + j * DIM, folding_randomness_global + (7 + j) * DIM)
    # Final folding: 5 challenges -> offsets 60..85
    for j in unroll(0, 5):
        copy_5(all_folding_randomness[2] + j * DIM, folding_randomness_global + (12 + j) * DIM)
    # Final sumcheck: 8 challenges -> offsets 85..125
    for j in unroll(0, 8):
        copy_5(all_folding_randomness[3] + j * DIM, folding_randomness_global + (17 + j) * DIM)

    # OOD recovery at commitment: oods[0]=2, n_vars=25
    all_ood_recovered_evals = Array(2 * DIM)
    for i in unroll(0, 2):
        expanded_from_univariate = expand_from_univariate_ext_const(ood_points_commit + i * DIM, 25)
        poly_eq_ee(expanded_from_univariate, folding_randomness_global, all_ood_recovered_evals + i * DIM, 25)
    s: Mut = Array(DIM)
    dot_product_ee(all_ood_recovered_evals, combination_randomness_powers_0, s, 2)

    # Round 0 consistency: n_vars_remaining=18, oods[1]=1, queries=113
    my_folding_randomness_0 = folding_randomness_global + 7 * DIM
    combination_randomness_powers_r0 = all_combination_randomness_powers[0]
    # Single OOD point (dot_product_ee with n=1 and powers[0]=1 is identity)
    expanded_ood_0 = expand_from_univariate_ext_const(all_ood_points[0], 18)
    summed_ood_0 = Array(DIM)
    poly_eq_ee(expanded_ood_0, my_folding_randomness_0, summed_ood_0, 18)
    # 113 query checks
    s6s_0 = Array(113 * DIM)
    circle_value_0 = all_circle_values[0]
    for j in range(0, 113):
        expanded_q = expand_from_univariate_base_const(circle_value_0[j], 18)
        poly_eq_be(expanded_q, my_folding_randomness_0, s6s_0 + j * DIM, 18)
    s7_0 = Array(DIM)
    dot_product_ee(s6s_0, combination_randomness_powers_r0 + 1 * DIM, s7_0, 113)
    s = add_extension_ret(s, s7_0)
    s = add_extension_ret(summed_ood_0, s)

    # Round 1 consistency: n_vars_remaining=13, oods[2]=2, queries=55
    my_folding_randomness_1 = folding_randomness_global + 12 * DIM
    combination_randomness_powers_r1 = all_combination_randomness_powers[1]
    # Two OOD points
    my_ood_recovered_evals_1 = Array(2 * DIM)
    for j in unroll(0, 2):
        expanded_ood_1 = expand_from_univariate_ext_const(all_ood_points[1] + j * DIM, 13)
        poly_eq_ee(expanded_ood_1, my_folding_randomness_1, my_ood_recovered_evals_1 + j * DIM, 13)
    summed_ood_1 = Array(DIM)
    dot_product_ee(my_ood_recovered_evals_1, combination_randomness_powers_r1, summed_ood_1, 2)
    # 55 query checks
    s6s_1 = Array(55 * DIM)
    circle_value_1 = all_circle_values[1]
    for j in range(0, 55):
        expanded_q = expand_from_univariate_base_const(circle_value_1[j], 13)
        poly_eq_be(expanded_q, my_folding_randomness_1, s6s_1 + j * DIM, 13)
    s7_1 = Array(DIM)
    dot_product_ee(s6s_1, combination_randomness_powers_r1 + 2 * DIM, s7_1, 55)
    s = add_extension_ret(s, s7_1)
    s = add_extension_ret(summed_ood_1, s)

    # Final value: n_final_vars=8
    final_value = eval_multilinear_coeffs_rev(final_coefficients, all_folding_randomness[3], 8)

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


def sumcheck_verify_unrolled(fs: Mut, n_steps: Const, claimed_sum: Mut, degree: Const):
    challenges = Array(n_steps * DIM)
    for sc_round in unroll(0, n_steps):
        fs, poly = fs_receive_ef_inlined(fs, degree + 1)
        sum_over_boolean_hypercube = polynomial_sum_at_0_and_1(poly, degree)
        copy_5(sum_over_boolean_hypercube, claimed_sum)
        fs, rand = fs_sample_ef(fs)
        claimed_sum = univariate_polynomial_eval(poly, rand, degree)
        copy_5(rand, challenges + sc_round * DIM)
    return fs, challenges, claimed_sum




def decompose_and_verify_merkle_batch_const(num_queries, sampled, root, height: Const, num_chunks: Const, circle_values, merkle_leaves):
    for i in range(0, num_queries):
        nibbles, circle_values[i] = checked_decompose_bits_and_compute_root_pow_const(sampled[i], height)
        merkle_leaves[i] = hash_and_verify_merkle_hint(nibbles, root, height, num_chunks)
    return


def sample_stir_indexes_and_fold_r0(fs: Mut, prev_root, folding_randomness):
    # Round 0: 113 queries, basefield, fold=7, 2^7=128, domain=27, qgrind=17
    # folded_domain=20, chunks=128/8=16
    fs = fs_grinding(fs, 17)
    sampled = fs_sample_data_with_offset(fs, 15, 0)
    fs = fs_finalize_sample(fs, 15)
    merkle_leaves = Array(113)
    circle_values = Array(113)
    decompose_and_verify_merkle_batch_const(113, sampled, prev_root, 20, 16, circle_values, merkle_leaves)
    folds = Array(113 * DIM)
    poly_eq = poly_eq_extension(folding_randomness, 7)
    for i in range(0, 113):
        dot_product_be(merkle_leaves[i], poly_eq, folds + i * DIM, 128)
    return fs, circle_values, folds


def sample_stir_indexes_and_fold_r1(fs: Mut, prev_root, folding_randomness):
    # Round 1: 55 queries, ext field, fold=5, 2^5=32, domain=22, qgrind=16
    # folded_domain=17, chunks=32*5/8=20
    fs = fs_grinding(fs, 16)
    sampled = fs_sample_data_with_offset(fs, 7, 0)
    fs = fs_finalize_sample(fs, 7)
    merkle_leaves = Array(55)
    circle_values = Array(55)
    decompose_and_verify_merkle_batch_const(55, sampled, prev_root, 17, 20, circle_values, merkle_leaves)
    folds = Array(55 * DIM)
    poly_eq = poly_eq_extension(folding_randomness, 5)
    for i in range(0, 55):
        dot_product_ee(merkle_leaves[i], poly_eq, folds + i * DIM, 32)
    return fs, circle_values, folds


def sample_stir_indexes_and_fold_final(fs: Mut, prev_root, folding_randomness):
    # Final: 27 queries, ext field, fold=5, 2^5=32, domain=21, qgrind=16
    # folded_domain=16, chunks=32*5/8=20
    fs = fs_grinding(fs, 16)
    sampled = fs_sample_data_with_offset(fs, 4, 0)
    fs = fs_finalize_sample(fs, 4)
    merkle_leaves = Array(27)
    circle_values = Array(27)
    decompose_and_verify_merkle_batch_const(27, sampled, prev_root, 16, 20, circle_values, merkle_leaves)
    folds = Array(27 * DIM)
    poly_eq = poly_eq_extension(folding_randomness, 5)
    for i in range(0, 27):
        dot_product_ee(merkle_leaves[i], poly_eq, folds + i * DIM, 32)
    return fs, circle_values, folds


def whir_round_0(fs: Mut, prev_root, claimed_sum):
    # Round 0: fold=7, 2^7=128, first_round=1, queries=113, domain=27, qgrind=17, oods=1, fgrind=0
    fs, folding_randomness, new_claimed_sum_a = sumcheck_verify_unrolled(fs, 7, claimed_sum, 2)

    fs, root, ood_points, ood_evals = parse_whir_commitment_const(fs, 1)

    fs, circle_values, folds = sample_stir_indexes_and_fold_r0(fs, prev_root, folding_randomness)

    fs, combination_randomness_gen = fs_sample_ef(fs)
    combination_randomness_powers = powers_const(combination_randomness_gen, 114)

    # dot_product_ee(ood_evals, powers, res, 1) = ood_evals[0] * powers[0] = ood_evals (powers[0]=1)
    claimed_sum_1 = Array(DIM)
    dot_product_ee(folds, combination_randomness_powers + 1 * DIM, claimed_sum_1, 113)

    new_claimed_sum_b = add_extension_ret(ood_evals, claimed_sum_1)
    final_sum = add_extension_ret(new_claimed_sum_a, new_claimed_sum_b)

    return (fs, folding_randomness, ood_points, root, circle_values, combination_randomness_powers, final_sum)


def whir_round_1(fs: Mut, prev_root, claimed_sum):
    # Round 1: fold=5, 2^5=32, first_round=0, queries=55, domain=22, qgrind=16, oods=2, fgrind=0
    fs, folding_randomness, new_claimed_sum_a = sumcheck_verify_unrolled(fs, 5, claimed_sum, 2)

    fs, root, ood_points, ood_evals = parse_whir_commitment_const(fs, 2)

    fs, circle_values, folds = sample_stir_indexes_and_fold_r1(fs, prev_root, folding_randomness)

    fs, combination_randomness_gen = fs_sample_ef(fs)
    combination_randomness_powers = powers_const(combination_randomness_gen, 57)

    claimed_sum_0 = Array(DIM)
    dot_product_ee(ood_evals, combination_randomness_powers, claimed_sum_0, 2)

    claimed_sum_1 = Array(DIM)
    dot_product_ee(folds, combination_randomness_powers + 2 * DIM, claimed_sum_1, 55)

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



def parse_whir_commitment_const(fs: Mut, num_ood: Const):
    fs, root = fs_receive_chunks(fs, 1)
    fs, ood_points = fs_sample_many_ef(fs, num_ood)
    fs, ood_evals = fs_receive_ef_inlined(fs, num_ood)
    return fs, root, ood_points, ood_evals


def get_num_oods(log_inv_rate, n_vars):
    # Hardcoded for n_vars=25, log_inv_rate=2
    assert log_inv_rate == 2
    assert n_vars == 25
    num_oods = Array(3)
    num_oods[0] = 2
    num_oods[1] = 1
    num_oods[2] = 2
    return num_oods
