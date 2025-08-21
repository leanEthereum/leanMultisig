use std::marker::PhantomData;

use compiler::compile_program;
use p3_field::BasedVectorSpace;
use p3_field::PrimeCharacteristicRing;
use pcs::WhirBatchPcs;
use rand::{Rng, SeedableRng, rngs::StdRng};
use utils::{
    MY_DIGEST_ELEMS, MyMerkleCompress, MyMerkleHash, build_merkle_compress, build_merkle_hash,
    build_prover_state, build_verifier_state,
};
use vm::*;
use whir_p3::{
    dft::EvalsDft,
    poly::{evals::EvaluationsList, multilinear::*},
    whir::{
        committer::{reader::*, writer::*},
        config::{FoldingFactor, SecurityAssumption, WhirConfig, WhirConfigBuilder},
        prover::*,
        statement::Statement,
        verifier::*,
    },
};

use crate::prove_execution::prove_execution;
use crate::verify_execution::verify_execution;

#[test]
pub fn test_whir_verif() {
    run_whir_verif();
}

pub fn run_whir_verif() {
    let program_str = r#"

    // 1 OOD QUERY PER ROUND, 0 GRINDING

    const W = 3; // in the extension field, X^8 = 3
    const F_BITS = 31; // koala-bear = 31 bits

    const N_VARS = 25;
    const LOG_INV_RATE = 2; 
    const N_ROUNDS = 3;
    
    const PADDING_FOR_INITIAL_MERKLE_LEAVES = 7;

    const FOLDING_FACTOR_0 = 7;
    const FOLDING_FACTOR_1 = 4;
    const FOLDING_FACTOR_2 = 4;
    const FOLDING_FACTOR_3 = 4;

    const FINAL_VARS = N_VARS - (FOLDING_FACTOR_0 + FOLDING_FACTOR_1 + FOLDING_FACTOR_2 + FOLDING_FACTOR_3);

    const RS_REDUCTION_FACTOR_0 = 3;
    const RS_REDUCTION_FACTOR_1 = 1;
    const RS_REDUCTION_FACTOR_2 = 1;
    const RS_REDUCTION_FACTOR_3 = 1;

    const NUM_QUERIES_0 = 58;
    const NUM_QUERIES_1 = 19;
    const NUM_QUERIES_2 = 13;
    const NUM_QUERIES_3 = 10;

    const GRINDING_BITS_0 = 16;
    const GRINDING_BITS_1 = 15;
    const GRINDING_BITS_2 = 11;
    const GRINDING_BITS_3 = 8;

    const TWO_ADICITY = 24;
    const ROOT = 1791270792; // of order 2^TWO_ADICITY

    fn main() {
        transcript_start = public_input_start / 8;
        fs_state = fs_new(transcript_start);

        fs_state_0, root_0, ood_point_0, ood_eval_0 = parse_commitment(fs_state);

        // In the future point / eval will come from the PIOP
        fs_state_1, pcs_point = fs_hint(fs_state_0, N_VARS);
        fs_state_2, pcs_eval = fs_hint(fs_state_1, 1);
        fs_state_3, _ = fs_hint(fs_state_2, PADDING_FOR_INITIAL_MERKLE_LEAVES);
        fs_state_4, combination_randomness_gen_0 = fs_sample_ef(fs_state_3);  // vectorized pointer of len 1

        claimed_sum_side = mul_extension_ret(combination_randomness_gen_0, pcs_eval);
        claimed_sum_0 = add_extension_ret(ood_eval_0, claimed_sum_side);
        domain_size_0 = N_VARS + LOG_INV_RATE;
        fs_state_5, folding_randomness_1, ood_point_1, root_1, circle_values_1, combination_randomness_powers_1, claimed_sum_1 = 
            whir_round(fs_state_4, root_0, FOLDING_FACTOR_0, 2**FOLDING_FACTOR_0, 1, NUM_QUERIES_0, domain_size_0, claimed_sum_0, GRINDING_BITS_0);

        domain_size_1 = domain_size_0 - RS_REDUCTION_FACTOR_0;
        fs_state_6, folding_randomness_2, ood_point_2, root_2, circle_values_2, combination_randomness_powers_2, claimed_sum_2 = 
            whir_round(fs_state_5, root_1, FOLDING_FACTOR_1, 2**FOLDING_FACTOR_1, 0, NUM_QUERIES_1, domain_size_1, claimed_sum_1, GRINDING_BITS_1);

        domain_size_2 = domain_size_1 - RS_REDUCTION_FACTOR_1;
        fs_state_7, folding_randomness_3, ood_point_3, root_3, circle_values_3, combination_randomness_powers_3, claimed_sum_3 = 
            whir_round(fs_state_6, root_2, FOLDING_FACTOR_2, 2**FOLDING_FACTOR_2, 0, NUM_QUERIES_2, domain_size_2, claimed_sum_2, GRINDING_BITS_2);

        domain_size_3 = domain_size_2 - RS_REDUCTION_FACTOR_2;
        fs_state_8, folding_randomness_4, final_claimed_sum = sumcheck(fs_state_7, FOLDING_FACTOR_3, claimed_sum_3);
        fs_state_9, final_coeffcients = fs_receive(fs_state_8, 2**FINAL_VARS);
        fs_state_10, final_circle_values, final_folds =
            sample_stir_indexes_and_fold(fs_state_9, NUM_QUERIES_3, 0, FOLDING_FACTOR_3, 2**FOLDING_FACTOR_3, domain_size_3, root_3, folding_randomness_4, GRINDING_BITS_3);

        
        for i in 0..NUM_QUERIES_3 {
            powers_of_2_rev = powers_of_two_rev_base(final_circle_values[i], FINAL_VARS);
            poly_eq = poly_eq_base(powers_of_2_rev, FINAL_VARS, 2**FINAL_VARS);
            final_pol_evaluated_on_circle = malloc_vec(1);
            dot_product_base_extension(poly_eq, final_coeffcients, final_pol_evaluated_on_circle, 2**FINAL_VARS); // TODO use multilinear eval instead
            assert_eq_extension(final_pol_evaluated_on_circle, final_folds + i);
        }

        fs_state_11, folding_randomness_5, end_sum = sumcheck(fs_state_10, FINAL_VARS, final_claimed_sum);

        folding_randomness_global = malloc_vec(N_VARS);

        ffs = malloc(N_ROUNDS + 2);
        ffs[0] = FOLDING_FACTOR_0; ffs[1] = FOLDING_FACTOR_1; ffs[2] = FOLDING_FACTOR_2; ffs[3] = FOLDING_FACTOR_3; ffs[4] = FINAL_VARS;
        frs = malloc(N_ROUNDS + 2);
        frs[0] = folding_randomness_5; frs[1] = folding_randomness_4; frs[2] = folding_randomness_3; frs[3] = folding_randomness_2; frs[4] = folding_randomness_1;
        ffs_sums = malloc(N_ROUNDS + 2);
        ffs_sums[0] = FOLDING_FACTOR_0;
        for i in 0..N_ROUNDS + 1 {
            ffs_sums[i + 1] = ffs_sums[i] + ffs[i + 1];
        }
        for i in 0..N_ROUNDS + 2 {
            start = folding_randomness_global + N_VARS - ffs_sums[N_ROUNDS + 1 - i];
            for j in 0..ffs[N_ROUNDS + 1 - i] {
                copy_chunk_vec(frs[i] + j, start + j);
            }
        }

        ood_0_expanded_from_univariate = powers_of_two_rev_extension(ood_point_0, N_VARS);
        s0 = eq_mle_extension(ood_0_expanded_from_univariate, folding_randomness_global, N_VARS);
        s1 = eq_mle_extension(pcs_point, folding_randomness_global, N_VARS);
        s3 = mul_extension_ret(s1, combination_randomness_gen_0);
        s4 = add_extension_ret(s0, s3);

        weight_sums = malloc(N_ROUNDS + 1);
        weight_sums[0] = s4;

        ood_points = malloc(N_ROUNDS + 1); ood_points[0] = ood_point_0; ood_points[1] = ood_point_1; ood_points[2] = ood_point_2; ood_points[3] = ood_point_3;
        num_queries = malloc(N_ROUNDS + 1); num_queries[0] = NUM_QUERIES_0; num_queries[1] = NUM_QUERIES_1; num_queries[2] = NUM_QUERIES_2; num_queries[3] = NUM_QUERIES_3;
        circle_values = malloc(N_ROUNDS + 1); circle_values[0] = circle_values_1; circle_values[1] = circle_values_2; circle_values[2] = circle_values_3; circle_values[3] = final_circle_values;
        combination_randomness_powers = malloc(N_ROUNDS); combination_randomness_powers[0] = combination_randomness_powers_1; combination_randomness_powers[1] = combination_randomness_powers_2; combination_randomness_powers[2] = combination_randomness_powers_3;

        for i in 0..N_ROUNDS {
            ood_expanded_from_univariate = powers_of_two_rev_extension(ood_points[i + 1], N_VARS - ffs_sums[i]); // 456 cycles
            s5 = eq_mle_extension(ood_expanded_from_univariate, folding_randomness_global, N_VARS - ffs_sums[i]); // 2248 cycles
            s6s = malloc_vec(num_queries[i] + 1);
            copy_chunk_vec(s5, s6s);
            circle_value_i = circle_values[i];
            for j in 0..num_queries[i] {
                expanded_from_univariate = powers_of_two_rev_base(circle_value_i[j], N_VARS - ffs_sums[i]); // 302 cycles
                temp = eq_mle_extension_base(expanded_from_univariate, folding_randomness_global, N_VARS - ffs_sums[i]); // 1415 cycles
                copy_chunk_vec(temp, s6s + j + 1);
            }
            s7 = malloc_vec(1);
            dot_product_dynamic(s6s, combination_randomness_powers[i], s7, num_queries[i] + 1);  // 10720 cycles
            wsum = add_extension_ret(weight_sums[i], s7);
            weight_sums[i+1] = wsum;
        }

        evaluation_of_weights = weight_sums[N_ROUNDS];
        poly_eq_final = poly_eq_extension(folding_randomness_5, FINAL_VARS, 2**FINAL_VARS);
        final_value = malloc_vec(1);
        dot_product(poly_eq_final, final_coeffcients, final_value, 2**FINAL_VARS);
        evaluation_of_weights_times_final_value = mul_extension_ret(evaluation_of_weights, final_value);
        assert_eq_extension(evaluation_of_weights_times_final_value, end_sum);
        return;
    }

    fn eq_mle_extension(a, b, n) -> 1 {

        buff = malloc_vec(n);

        for i in 0..n {
            ai = a + i;
            bi = b + i;
            buffi = buff + i;
            ab = mul_extension_ret(ai, bi);
            a_ptr = ai * 8;
            b_ptr = bi * 8;
            ab_ptr = ab * 8;
            buff_ptr = buffi * 8;
            buff_ptr[0] = 1 + 2 * ab_ptr[0] - a_ptr[0] - b_ptr[0];
            for j in 1..8 unroll {
                buff_ptr[j] = 2 * ab_ptr[j] - a_ptr[j] - b_ptr[j];
            }
        }

        prods = malloc_vec(n);
        copy_chunk_vec(buff, prods);
        for i in 0..n - 1 {
            mul_extension(prods + i, buff + i + 1, prods + i + 1);
        }

        return prods + n - 1;
    }

    fn eq_mle_extension_base(a, b, n) -> 1 {
        // a: base
        // b: extension

        buff = malloc_vec(n);

        for i in 0..n {
            ai = a[i];
            bi = (b + i) * 8;
            buffi = (buff + i) * 8;
            ai_double = ai * 2;
            buffi[0] = 1 + ai_double * bi[0] - ai - bi[0];
            for j in 1..8 unroll {
                buffi[j] = ai_double * bi[j] - bi[j];
            }
        }


        prods = malloc_vec(n);
        copy_chunk_vec(buff, prods);
        for i in 0..n - 1 {
            mul_extension(prods + i, buff + i + 1, prods + i + 1);
        }
        return prods + n - 1;
    }

    fn powers_of_two_rev_base(alpha, n) -> 1 {
        // "expand_from_univariate"
        // alpha: F

        res = malloc(n);
        res[n - 1] = alpha;
        for i in 1..n {
            res[n - 1 - i] = res[n - i] * res[n - i];
        }
        return res;
    }

    fn powers_of_two_rev_extension(alpha, n) -> 1 {
        // "expand_from_univariate"

        res = malloc_vec(n);
        copy_chunk_vec(alpha, res + n - 1);
        for i in 1..n {
            mul_extension(res + (n - i), res + (n - i), res + (n - 1 - i));
        }
        return res;
    }

    fn sumcheck(fs_state, n_steps, claimed_sum) -> 3 {
        fs_states_a = malloc(n_steps + 1);
        fs_states_a[0] = fs_state;

        claimed_sums = malloc(n_steps + 1);
        claimed_sums[0] = claimed_sum;

        folding_randomness = malloc_vec(n_steps); // in reverse order.

        for sc_round in 0..n_steps {
            fs_state_5, poly = fs_receive(fs_states_a[sc_round], 3); // vectorized pointer of len 1
            sum_over_boolean_hypercube = degree_two_polynomial_sum_at_0_and_1(poly);
            assert_eq_extension(sum_over_boolean_hypercube, claimed_sums[sc_round]);
            fs_state_6, rand = fs_sample_ef(fs_state_5);  // vectorized pointer of len 1
            fs_states_a[sc_round + 1] = fs_state_6;
            new_claimed_sum = degree_two_polynomial_eval(poly, rand);
            claimed_sums[sc_round + 1] = new_claimed_sum;
            copy_chunk_vec(rand, folding_randomness +  n_steps - 1 - sc_round);
        }
        new_state = fs_states_a[n_steps];
        new_claimed_sum = claimed_sums[n_steps];

        return new_state, folding_randomness, new_claimed_sum;
    }

    fn sample_stir_indexes_and_fold(fs_state, num_queries, is_first_round, folding_factor, two_pow_folding_factor, domain_size, prev_root, folding_randomness, grinding_bits) -> 3 {

        fs_state_8 = fs_grinding(fs_state, grinding_bits);
        fs_state_9, stir_challenges_indexes = sample_bits(fs_state_8, num_queries);

        answers = malloc(num_queries); // a vector of vectorized pointers, each pointing to `two_pow_folding_factor` field elements (base if first rounds, extension otherwise)
        fs_states_b = malloc(num_queries + 1);
        fs_states_b[0] = fs_state_9;
        
        // the number of chunk of 8 field elements per merkle leaf opened
        if is_first_round == 1 {
            n_chuncks_per_answer = two_pow_folding_factor / 8; // "/ 8" because initial merkle leaves are in the basefield
        } else {
            n_chuncks_per_answer = two_pow_folding_factor;
        }

        for i in 0..num_queries {
            new_fs_state, answer = fs_hint(fs_states_b[i], n_chuncks_per_answer); 
            fs_states_b[i + 1] = new_fs_state;
            answers[i] = answer;
        }
        fs_state_10 = fs_states_b[num_queries];

        leaf_hashes = malloc(num_queries); // a vector of vectorized pointers, each pointing to 1 chunk of 8 field elements
        for i in 0..num_queries {
            answer = answers[i];
            internal_states = malloc(1 + (n_chuncks_per_answer / 2)); // "/ 2" because with poseidon24 we hash 2 chuncks of 8 field elements at each permutation
            internal_states[0] = pointer_to_zero_vector; // initial state
            for j in 0..n_chuncks_per_answer / 2 {
                new_state = poseidon24(answer + (2*j), internal_states[j]);
                internal_states[j + 1] = new_state;
            }
            leaf_hashes[i] = internal_states[n_chuncks_per_answer / 2];
        }

        folded_domain_size = domain_size - folding_factor;

        fs_states_c = malloc(num_queries + 1);
        fs_states_c[0] = fs_state_10;

        for i in 0..num_queries {
            fs_state_11, merkle_path = fs_hint(fs_states_c[i], folded_domain_size);
            fs_states_c[i + 1] = fs_state_11;

            stir_index_bits = stir_challenges_indexes[i]; // a pointer to 31 bits

            states = malloc(1 + folded_domain_size);
            states[0] = leaf_hashes[i];
            for j in 0..folded_domain_size {
                if stir_index_bits[j] == 1 {
                    left = merkle_path + j;
                    right = states[j];
                } else {
                    left = states[j];
                    right = merkle_path + j;
                }
                state_j_plus_1 = poseidon16(left, right);
                states[j + 1] = state_j_plus_1;
            }
            assert_eq_extension(states[folded_domain_size], prev_root);
        }

        fs_state_11 = fs_states_c[num_queries];

        folds = malloc_vec(num_queries);
        if is_first_round == 1 {
            for i in 0..num_queries {
                multilinear_eval((answers[i] * 8) / 2**FOLDING_FACTOR_0, folding_randomness, folds + i, FOLDING_FACTOR_0); // TODO batching: use a single call to multilinear eval
            }
        } else {
            poly_eq = poly_eq_extension(folding_randomness, folding_factor, two_pow_folding_factor);
            for i in 0..num_queries {
                dot_product_dynamic(answers[i], poly_eq, folds + i, two_pow_folding_factor);
            }
        }

        circle_values = malloc(num_queries); // ROOT^each_stir_index
        for i in 0..num_queries {
            stir_index_bits = stir_challenges_indexes[i];
            circle_value = unit_root_pow(folded_domain_size, stir_index_bits);
            circle_values[i] = circle_value;
        }

        return fs_state_11, circle_values, folds;
    }


    fn whir_round(fs_state, prev_root, folding_factor, two_pow_folding_factor, is_first_round, num_queries, domain_size, claimed_sum, grinding_bits) -> 7 {
        fs_state_7, folding_randomness, new_claimed_sum_a = sumcheck(fs_state, folding_factor, claimed_sum);

        fs_state_8, root, ood_point, ood_eval = parse_commitment(fs_state_7);
   
        fs_state_11, circle_values, folds = 
            sample_stir_indexes_and_fold(fs_state_8, num_queries, is_first_round, folding_factor, two_pow_folding_factor, domain_size, prev_root, folding_randomness, grinding_bits);

        fs_state_12, combination_randomness_gen = fs_sample_ef(fs_state_11);

        combination_randomness_powers = powers(combination_randomness_gen, num_queries + 1); // "+ 1" because of one OOD sample

        claimed_sum_supplement_side = malloc_vec(1);
        dot_product_dynamic(folds, combination_randomness_powers + 1, claimed_sum_supplement_side, num_queries);
        claimed_sum_supplement = add_extension_ret(claimed_sum_supplement_side, ood_eval);
        new_claimed_sum_b = add_extension_ret(claimed_sum_supplement, new_claimed_sum_a);

        return fs_state_12, folding_randomness, ood_point, root, circle_values, combination_randomness_powers, new_claimed_sum_b;
    }

    fn copy_chunk(src, dst) {
        // src: pointer to 8 F
        // dst: pointer to 8 F
        for i in 0..8 unroll { dst[i] = src[i]; }
        return;
    }

    fn copy_chunk_vec(src, dst) {
        zero = 0; // TODO
        add_extension(src, zero, dst);
        return;
    }

    fn powers(alpha, n) -> 1 {
        // alpha: EF
        // n: F

        res = malloc_vec(n);
        set_to_one(res);
        for i in 0..n - 1 {
            mul_extension(res + i, alpha, res + i + 1);
        }
        return res;
    }

    fn unit_root_pow(domain_size, index_bits) -> 1 {
        // index_bits is a pointer to domain_size bits
        if domain_size == 19 {
            res = unit_root_pow_const(19, index_bits);
            return res;
        }
        if domain_size == 18 {
            res = unit_root_pow_const(18, index_bits);
            return res;
        }
        if domain_size == 17 {
            res = unit_root_pow_const(17, index_bits);
            return res;
        }
        if domain_size == 16 {
            res = unit_root_pow_const(16, index_bits);
            return res;
        }
        if domain_size == 15 {
            res = unit_root_pow_const(15, index_bits);
            return res;
        }
        if domain_size == 20 {
            res = unit_root_pow_const(20, index_bits);
            return res;
        }
        UNIMPLEMENTED = 0;
        print(UNIMPLEMENTED, domain_size);
        panic();
    }

    fn unit_root_pow_const(const domain_size, index_bits) -> 1 {
        prods = malloc(domain_size);
        prods[0] = ((index_bits[0] * ROOT**(2**(TWO_ADICITY - domain_size))) + (1 - index_bits[0]));
        for i in 1..domain_size unroll {
            prods[i] = prods[i - 1] * ((index_bits[i] * ROOT**(2**(TWO_ADICITY - domain_size + i))) + (1 - index_bits[i]));
        }
        return prods[domain_size - 1];
    }

    fn dot_product_dynamic(a, b, res, n) {
        if n == 16 {
            dot_product(a, b, res, 16);
            return;
        }
        if n == NUM_QUERIES_0 {
            dot_product(a, b, res, NUM_QUERIES_0);
            return;
        }
        if n == NUM_QUERIES_1 {
            dot_product(a, b, res, NUM_QUERIES_1);
            return;
        }
        if n == NUM_QUERIES_2 {
            dot_product(a, b, res, NUM_QUERIES_2);
            return;
        }
        if n == NUM_QUERIES_3 {
            dot_product(a, b, res, NUM_QUERIES_3);
            return;
        }
        if n == NUM_QUERIES_0 + 1 {
            dot_product(a, b, res, NUM_QUERIES_0 + 1);
            return;
        }
        if n == NUM_QUERIES_1 + 1 {
            dot_product(a, b, res, NUM_QUERIES_1 + 1);
            return;
        }
        if n == NUM_QUERIES_2 + 1 {
            dot_product(a, b, res, NUM_QUERIES_2 + 1);
            return;
        }
        if n == NUM_QUERIES_3 + 1 {
            dot_product(a, b, res, NUM_QUERIES_3 + 1);
            return;
        }

        TODO_dot_product_dynamic = 0;
        print(TODO_dot_product_dynamic, n);
        panic();
    }

    // fn dot_product(a, b, res, const n) {
    //     prods = malloc_vec(n);
    //     for i in 0..n unroll {
    //         mul_extension(a + i, b + i, prods + i);
    //     }

    //     sums = malloc_vec(n);
    //     copy_chunk_vec(prods, sums);
    //     for i in 0..n - 1 unroll {
    //         add_extension(sums + i, prods + i + 1, sums + i + 1);
    //     }

    //     copy_chunk_vec(sums + n - 1, res);

    //     return;
    // }


    fn dot_product_base_extension(a, b, res, const n) {
        // a is a pointer to n base field elements
        // b is a pointer to n extension field elements

        b_ptr = b * 8;
        res_ptr = res * 8;
           
        prods = malloc(n * 8);
        for i in 0..n unroll {
            for j in 0..8 unroll {
                prods[i * 8 + j] = a[i] * b_ptr[i * 8 + j];
            }
        }
        my_buff = malloc(n * 8);
        for i in 0..8 unroll {
            my_buff[n * i] = prods[i];
            for j in 0..n - 1 unroll {
                my_buff[(n * i) + j + 1] = my_buff[(n * i) + j] + prods[i + ((j + 1) * 8)];
            }
            res_ptr[i] = my_buff[(n * i) + n - 1];
        }

        return;
    }

    fn poly_eq_extension(point, n, two_pow_n) -> 1 {
        // Example: for n = 2: eq(x, y) = [(1 - x)(1 - y), (1 - x)y, x(1 - y), xy]

        if n == 0 {
            res = malloc_vec(1);
            set_to_one(res);
            return res;
        }

        res = malloc_vec(two_pow_n);

        inner_res = poly_eq_extension(point + 1, n - 1, two_pow_n / 2);

        two_pow_n_minus_1 = two_pow_n / 2;

        for i in 0..two_pow_n_minus_1 {
            mul_extension(point, inner_res + i, res + two_pow_n_minus_1 + i);
            sub_extension(inner_res + i, res + two_pow_n_minus_1 + i, res + i);
        }
        
        return res;
    }

    fn poly_eq_base(point, n, two_pow_n) -> 1 {
        // return a (normal) pointer to 2^n base field elements, corresponding to the "equality polynomial" at point
        // Example: for n = 2: eq(x, y) = [(1 - x)(1 - y), (1 - x)y, x(1 - y), xy]

        if n == 0 {
            // base case
            res = malloc(1);
            res[0] = 1;
            return res;
        }

        res = malloc(two_pow_n);

        inner_res = poly_eq_base(point + 1, n - 1, two_pow_n / 2);

        two_pow_n_minus_1 = two_pow_n / 2;

        for i in 0..two_pow_n_minus_1 {
            res[two_pow_n_minus_1 + i] = inner_res[i] * point[0];
            res[i] = inner_res[i] - res[two_pow_n_minus_1 + i];
        }
        
        return res;
    }


    fn pow(a, b) -> 1 {
        if b == 0 {
            return 1; // a^0 = 1
        } else {
            p = pow(a, b - 1);
            return a * p;
        }
    }

    fn sample_bits(fs_state, n) -> 2 {
        // return the updated fs_state, and a pointer to n pointers, each pointing to 31 (boolean) field elements
        samples = malloc(n);
        new_fs_state = fs_sample_helper(fs_state, n, samples);
        sampled_bits = malloc(n);
        for i in 0..n {
            bits = checked_decompose_bits(samples[i]);
            sampled_bits[i] = bits;
        }

        return new_fs_state, sampled_bits;
    }

    fn checked_decompose_bits(a) -> 1 {
        // return a pointer to bits of a
        bits = decompose_bits(a); // hint

        for i in 0..F_BITS unroll {
            assert bits[i] * (1 - bits[i]) == 0;
        }
        sums = malloc(F_BITS);
        sums[0] = bits[0];
        for i in 1..F_BITS unroll {
            sums[i] = sums[i - 1] + bits[i] * 2**i;
        }
        assert a == sums[F_BITS - 1];
        return bits;
    }

    fn degree_two_polynomial_sum_at_0_and_1(coeffs) -> 1 {
        // coeffs is a vectorized pointer to 3 chunks of 8 field elements
        // return a vectorized pointer to 1 chunk of 8 field elements
        a = add_extension_ret(coeffs, coeffs);
        b = add_extension_ret(a, coeffs + 1);
        c = add_extension_ret(b, coeffs + 2);
        return c;
    }

    fn degree_two_polynomial_eval(coeffs, point) -> 1 {
        // coefs: vectorized
        // res: normal pointer to 8 field elements
        point_squared = mul_extension_ret(point, point);
        a_xx = mul_extension_ret(coeffs + 2, point_squared);
        b_x = mul_extension_ret(coeffs + 1, point);
        c = coeffs;
        res_0 = add_extension_ret(a_xx, b_x);
        res_1 = add_extension_ret(res_0, c);
        return res_1;
    }

    fn parse_commitment(fs_state) -> 4 {
        fs_state_1, root = fs_receive(fs_state, 1); // vectorized pointer of len 1
        fs_state_2, ood_point = fs_sample_ef(fs_state_1);  // vectorized pointer of len 1
        fs_state_3, ood_eval = fs_receive(fs_state_2, 1); // vectorized pointer of len 1
        return fs_state_3, root, ood_point, ood_eval;
    }
    
    // FIAT SHAMIR layout:
    // 0 -> transcript (vectorized pointer)
    // 1 -> vectorized pointer to first half of sponge state
    // 2 -> vectorized pointer to second half of sponge state
    // 3 -> output_buffer_size

    fn fs_new(transcript) -> 1 {
        // transcript is a (vectorized) pointer
        // TODO domain separator
        fs_state = malloc(4);
        fs_state[0] = transcript;
        fs_state[1] = pointer_to_zero_vector; // first half of sponge state
        fs_state[2] = pointer_to_zero_vector; // second half of sponge state
        fs_state[3] = 0; // output buffer size

        return fs_state;
    }

     fn fs_grinding(fs_state, bits) -> 1 {
        // WARNING: should not be called 2 times in a row without duplexing in between

        if bits == 0 {
            return fs_state; // no grinding
        }

        transcript_ptr = fs_state[0] * 8;
        l_ptr = fs_state[1] * 8;
        
        new_l = malloc_vec(1);
        new_l_ptr = new_l * 8;
        new_l_ptr[0] = transcript_ptr[0];
        for i in 1..8 unroll {
            new_l_ptr[i] = l_ptr[i];
        }

        l_r_updated = poseidon16(new_l, fs_state[2]);
        new_fs_state = malloc(4);
        new_fs_state[0] = fs_state[0] + 1; // read one 1 chunk of 8 field elements (7 are useless)
        new_fs_state[1] = l_r_updated;
        new_fs_state[2] = l_r_updated + 1;
        new_fs_state[3] = 7; // output_buffer_size

        l_updated_ptr = l_r_updated* 8;
        sampled = l_updated_ptr[7];
        sampled_bits = checked_decompose_bits(sampled);
        for i in 0..bits {
            assert sampled_bits[i] == 0;
        }
        return new_fs_state;
    }

    fn less_than_8(a) -> 1 {
        if a * (a - 1) * (a - 2) * (a - 3) * (a - 4) * (a - 5) * (a - 6) * (a - 7) == 0 {
            return 1; // a < 8
        }
        return 0; // a >= 8
    }

    fn fs_sample(fs_state, n) -> 2 {
        // return the updated fs_state, and a pointer to n field elements
        res = malloc(n);
        new_fs_state = fs_sample_helper(fs_state, n, res);
        return new_fs_state, res;
    }

    fn fs_sample_ef(fs_state) -> 2 {
        // return the updated fs_state, and a vectorized pointer to 1 chunk of 8 field elements
        res = malloc_vec(1);
        new_fs_state = fs_sample_helper(fs_state, 8, res * 8);
        return new_fs_state, res;
    }

    fn fs_sample_helper(fs_state, n, res) -> 1 {
        // return the updated fs_state
        // fill res with n field elements

        output_buffer_size = fs_state[3];
        output_buffer_ptr = fs_state[1] * 8;

        for i in 0..n {
            if output_buffer_size - i == 0 {
                break;
            }
            res[i] = output_buffer_ptr[output_buffer_size - 1 - i];
        }

        finished = less_than_8(output_buffer_size - n);
        if finished == 1 {
            // no duplexing
            new_fs_state = malloc(4);
            new_fs_state[0] = fs_state[0];
            new_fs_state[1] = fs_state[1];
            new_fs_state[2] = fs_state[2];
            new_fs_state[3] = output_buffer_size - n;
            return new_fs_state;
        }

        // duplexing
        l_r = poseidon16(fs_state[1], fs_state[2]);
        new_fs_state = malloc(4);
        new_fs_state[0] = fs_state[0];
        new_fs_state[1] = l_r;
        new_fs_state[2] = l_r + 1;
        new_fs_state[3] = 8; // output_buffer_size

        remaining = n - output_buffer_size;
        if remaining == 0 {
            return new_fs_state;
        }

        shifted_res = res + output_buffer_size;
        final_res = fs_sample_helper(new_fs_state, remaining, shifted_res);
        return final_res;

    }

    fn fs_hint(fs_state, n) -> 2 {
        // return the updated fs_state, and a vectorized pointer to n chunk of 8 field elements

        res = fs_state[0];
        new_fs_state = malloc(4);
        new_fs_state[0] = res + n;
        new_fs_state[1] = fs_state[1];
        new_fs_state[2] = fs_state[2];
        new_fs_state[3] = fs_state[3];
        return new_fs_state, res; 
    }

    fn fs_receive(fs_state, n) -> 2 {
        // return the updated fs_state, and a vectorized pointer to n chunk of 8 field elements

        res = fs_state[0];
        final_fs_state = fs_observe(fs_state, n);
        return final_fs_state, res;
    }

    fn fs_observe(fs_state, n) -> 1 {
        // observe n chunk of 8 field elements from the transcript
        // and return the updated fs_state
        // duplexing
        l_r = poseidon16(fs_state[0], fs_state[2]);
        new_fs_state = malloc(4);
        new_fs_state[0] = fs_state[0] + 1;
        new_fs_state[1] = l_r;
        new_fs_state[2] = l_r + 1;
        new_fs_state[3] = 8; // output_buffer_size

        if n == 1 {
            return new_fs_state;
        } else {
            final_fs_state = fs_observe(new_fs_state, n - 1);
            return final_fs_state;
        }
    }

    fn fs_print_state(fs_state) {
        left = fs_state[1] * 8;
        for i in 0..8 {
            print(left[i]);
        }
        right = fs_state[2] * 8;
        for i in 0..8 {
            print(right[i]);
        }
        return;
    }

    fn mul_extension_ret(a, b) -> 1 {
        c = malloc_vec(1);
        mul_extension(a, b, c);
        return c;
    }

    // fn mul_extension(a, b, c) {
    //     // c = a * b

    //     ap = a * 8;
    //     bp = b * 8;
    //     cp = c * 8;
       
    //     cp[0] = (ap[0] * bp[0]) + W * ((ap[1] * bp[7]) + (ap[2] * bp[6]) + (ap[3] * bp[5]) + (ap[4] * bp[4]) + (ap[5] * bp[3]) + (ap[6] * bp[2]) + (ap[7] * bp[1]));
    //     cp[1] = (ap[1] * bp[0]) + (ap[0] * bp[1]) + W * ((ap[2] * bp[7]) + (ap[3] * bp[6]) + (ap[4] * bp[5]) + (ap[5] * bp[4]) + (ap[6] * bp[3]) + (ap[7] * bp[2]));
    //     cp[2] = (ap[2] * bp[0]) + (ap[1] * bp[1]) + (ap[0] * bp[2]) + W * ((ap[3] * bp[7]) + (ap[4] * bp[6]) + (ap[5] * bp[5]) + (ap[6] * bp[4]) + (ap[7] * bp[3]));
    //     cp[3] = (ap[3] * bp[0]) + (ap[2] * bp[1]) + (ap[1] * bp[2]) + (ap[0] * bp[3]) + W * ((ap[4] * bp[7]) + (ap[5] * bp[6]) + (ap[6] * bp[5]) + (ap[7] * bp[4]));
    //     cp[4] = (ap[4] * bp[0]) + (ap[3] * bp[1]) + (ap[2] * bp[2]) + (ap[1] * bp[3]) + (ap[0] * bp[4]) + W * ((ap[5] * bp[7]) + (ap[6] * bp[6]) + (ap[7] * bp[5]));
    //     cp[5] = (ap[5] * bp[0]) + (ap[4] * bp[1]) + (ap[3] * bp[2]) + (ap[2] * bp[3]) + (ap[1] * bp[4]) + (ap[0] * bp[5]) + W * ((ap[6] * bp[7]) + (ap[7] * bp[6]));
    //     cp[6] = (ap[6] * bp[0]) + (ap[5] * bp[1]) + (ap[4] * bp[2]) + (ap[3] * bp[3]) + (ap[2] * bp[4]) + (ap[1] * bp[5]) + (ap[0] * bp[6]) + W * (ap[7] * bp[7]);
    //     cp[7] = (ap[7] * bp[0]) + (ap[6] * bp[1]) + (ap[5] * bp[2]) + (ap[4] * bp[3]) + (ap[3] * bp[4]) + (ap[2] * bp[5]) + (ap[1] * bp[6]) + (ap[0] * bp[7]);

    //     return;
    // }

    fn mul_extension(a, b, c) {
        // c = a * b
        dot_product(a, b, c, 1);
        return;
    }

    fn add_extension_ret(a, b) -> 1 {
        c = malloc_vec(1);
        add_extension(a, b, c);
        return c;
    }

    fn add_extension(a, b, c) {
        // c = a + b

        ap = a * 8;
        bp = b * 8;
        cp = c * 8;

        for i in 0..8 unroll {
            cp[i] = ap[i] + bp[i];
        }
        return;
    }

    fn sub_extension(a, b, c) {
        // c = a - b

        ap = a * 8;
        bp = b * 8;
        cp = c * 8;

        for i in 0..8 unroll {
            cp[i] = ap[i] - bp[i];
        }
        return;
    }
    
    fn assert_eq_extension(a, b)  {
        null_ptr = pointer_to_zero_vector; // TODO avoid having to store this in a variable
        add_extension(a, null_ptr, b);
        return;
    }

    fn set_to_one(a) {
        a_ptr = 8 * a;
        a_ptr[0] = 1;
        for i in 1..8 unroll { a_ptr[i] = 0; }
        return;
    }

   fn print_chunk(a) {
        a_ptr = a * 8;
        for i in 0..8 {
            print(a_ptr[i]);
        }
        return;
    }

   "#;

    let num_variables = 25;
    let recursion_config_builder = WhirConfigBuilder {
        max_num_variables_to_send_coeffs: 6,
        security_level: 128,
        pow_bits: 17,
        folding_factor: FoldingFactor::ConstantFromSecondRound(7, 4),
        merkle_hash: build_merkle_hash(),
        merkle_compress: build_merkle_compress(),
        soundness_type: SecurityAssumption::CapacityBound,
        starting_log_inv_rate: 2,
        rs_domain_initial_reduction_factor: 3,
        base_field: PhantomData,
        extension_field: PhantomData,
    };

    let recursion_config = WhirConfig::<F, EF, MyMerkleHash, MyMerkleCompress, 8>::new(
        recursion_config_builder.clone(),
        num_variables,
    );
    assert_eq!(recursion_config.committment_ood_samples, 1);
    // println!("Whir parameters: {}", params.to_string());
    for (i, round) in recursion_config.round_parameters.iter().enumerate() {
        println!(
            "Round {}: {} queries, pow: {} bits",
            i, round.num_queries, round.pow_bits
        );
    }
    println!(
        "Final round: {} queries, pow: {} bits",
        recursion_config.final_queries, recursion_config.final_pow_bits
    );

    let mut rng = StdRng::seed_from_u64(0);
    let polynomial = (0..1 << num_variables)
        .map(|_| rng.random())
        .collect::<Vec<F>>();

    let point = MultilinearPoint::<EF>::rand(&mut rng, num_variables);

    let mut statement = Statement::<EF>::new(num_variables);
    let eval = polynomial.evaluate(&point);
    statement.add_constraint(point.clone(), eval);

    let mut prover_state = build_prover_state();

    // Commit to the polynomial and produce a witness
    let committer = Commiter(&recursion_config);

    let dft = EvalsDft::<F>::new(1 << recursion_config.max_fft_size());

    let witness = committer
        .commit(&dft, &mut prover_state, &polynomial)
        .unwrap();

    let mut public_input = prover_state.proof_data().to_vec();
    let commitment_size = public_input.len();
    assert_eq!(commitment_size, 16);
    public_input.extend(
        point
            .iter()
            .flat_map(|x| <EF as BasedVectorSpace<F>>::as_basis_coefficients_slice(x).to_vec()),
    );
    public_input.extend(<EF as BasedVectorSpace<F>>::as_basis_coefficients_slice(&eval).to_vec());

    let prover = Prover(&recursion_config);

    prover
        .prove(
            &dft,
            &mut prover_state,
            statement.clone(),
            witness,
            &polynomial,
        )
        .unwrap();

    let first_folding_factor = recursion_config_builder.folding_factor.at_round(0);
    let mut proof_data_padding = (1 << first_folding_factor)
        - ((PUBLIC_INPUT_START
            + public_input.len()
            + {
                // sumcheck polys
                first_folding_factor * 3 * DIMENSION
            }
            + {
                // merkle root
                MY_DIGEST_ELEMS
            }
            + {
                // grinding witness
                MY_DIGEST_ELEMS
            }
            + {
                // ood answer
                DIMENSION
            })
            % (1 << first_folding_factor));
    assert_eq!(proof_data_padding % 8, 0);
    proof_data_padding /= 8;
    println!(
        "1st merkle leaf padding: {} (vectorized)",
        proof_data_padding
    ); // to align the first merkle leaves (in base field)
    public_input.extend(F::zero_vec(proof_data_padding * 8));

    public_input.extend(prover_state.proof_data()[commitment_size..].to_vec());

    // Reconstruct verifier's view of the transcript using the DomainSeparator and prover's data
    let mut verifier_state = build_verifier_state(&prover_state);

    // Parse the commitment
    let parsed_commitment = CommitmentReader(&recursion_config)
        .parse_commitment(&mut verifier_state)
        .unwrap();

    Verifier(&recursion_config)
        .verify(&mut verifier_state, &parsed_commitment, &statement)
        .unwrap();

    // Validity Proof:

    // utils::init_tracing();
    let base_pcs = WhirConfigBuilder {
        folding_factor: FoldingFactor::ConstantFromSecondRound(7, 4),
        soundness_type: SecurityAssumption::CapacityBound,
        merkle_hash: build_merkle_hash(),
        merkle_compress: build_merkle_compress(),
        pow_bits: 16,
        max_num_variables_to_send_coeffs: 6,
        rs_domain_initial_reduction_factor: 5,
        security_level: 128,
        starting_log_inv_rate: 1,
        base_field: PhantomData::<F>,
        extension_field: PhantomData::<EF>,
    };

    let extension_pcs = WhirConfigBuilder {
        folding_factor: FoldingFactor::ConstantFromSecondRound(4, 4),
        soundness_type: SecurityAssumption::CapacityBound,
        merkle_hash: build_merkle_hash(),
        merkle_compress: build_merkle_compress(),
        pow_bits: 16,
        max_num_variables_to_send_coeffs: 6,
        rs_domain_initial_reduction_factor: 2,
        security_level: 128,
        starting_log_inv_rate: 1,
        base_field: PhantomData::<EF>,
        extension_field: PhantomData::<EF>,
    };

    let bytecode = compile_program(program_str);
    let batch_pcs = WhirBatchPcs(base_pcs, extension_pcs);
    let proof_data = prove_execution(&bytecode, &public_input, &[], &batch_pcs);
    verify_execution(&bytecode, &public_input, proof_data, &batch_pcs).unwrap();
}
