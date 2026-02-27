from snark_lib import *
from whir import *
from hashing import *

N_TABLES = N_TABLES_PLACEHOLDER

MIN_LOG_N_ROWS_PER_TABLE = MIN_LOG_N_ROWS_PER_TABLE_PLACEHOLDER
MAX_LOG_N_ROWS_PER_TABLE = MAX_LOG_N_ROWS_PER_TABLE_PLACEHOLDER
MIN_LOG_MEMORY_SIZE = MIN_LOG_MEMORY_SIZE_PLACEHOLDER
MAX_LOG_MEMORY_SIZE = MAX_LOG_MEMORY_SIZE_PLACEHOLDER
MAX_BUS_WIDTH = MAX_BUS_WIDTH_PLACEHOLDER
MAX_NUM_AIR_CONSTRAINTS = MAX_NUM_AIR_CONSTRAINTS_PLACEHOLDER

LOGUP_MEMORY_DOMAINSEP = LOGUP_MEMORY_DOMAINSEP_PLACEHOLDER
LOGUP_PRECOMPILE_DOMAINSEP = LOGUP_PRECOMPILE_DOMAINSEP_PLACEHOLDER
LOGUP_BYTECODE_DOMAINSEP = LOGUP_BYTECODE_DOMAINSEP_PLACEHOLDER
EXECUTION_TABLE_INDEX = EXECUTION_TABLE_INDEX_PLACEHOLDER

LOOKUPS_INDEXES = LOOKUPS_INDEXES_PLACEHOLDER  # [[_; ?]; N_TABLES]
LOOKUPS_VALUES = LOOKUPS_VALUES_PLACEHOLDER  # [[[_; ?]; ?]; N_TABLES]

NUM_COLS_AIR = NUM_COLS_AIR_PLACEHOLDER
NUM_COLS_TOTAL = NUM_COLS_TOTAL_PLACEHOLDER

AIR_DEGREES = AIR_DEGREES_PLACEHOLDER  # [_; N_TABLES]
N_AIR_COLUMNS = N_AIR_COLUMNS_PLACEHOLDER  # [_; N_TABLES]
AIR_DOWN_COLUMNS = AIR_DOWN_COLUMNS_PLACEHOLDER  # [[_; ?]; N_TABLES]

N_INSTRUCTION_COLUMNS = N_INSTRUCTION_COLUMNS_PLACEHOLDER
N_COMMITTED_EXEC_COLUMNS = N_COMMITTED_EXEC_COLUMNS_PLACEHOLDER

LOG_GUEST_BYTECODE_LEN = LOG_GUEST_BYTECODE_LEN_PLACEHOLDER
COL_PC = COL_PC_PLACEHOLDER
TOTAL_WHIR_STATEMENTS = TOTAL_WHIR_STATEMENTS_PLACEHOLDER
STARTING_PC = STARTING_PC_PLACEHOLDER
ENDING_PC = ENDING_PC_PLACEHOLDER
BYTECODE_POINT_N_VARS = LOG_GUEST_BYTECODE_LEN + log2_ceil(N_INSTRUCTION_COLUMNS)
BYTECODE_ZERO_EVAL = BYTECODE_ZERO_EVAL_PLACEHOLDER
BYTECODE_CLAIM_SIZE = (BYTECODE_POINT_N_VARS + 1) * DIM
BYTECODE_CLAIM_SIZE_PADDED = next_multiple_of(BYTECODE_CLAIM_SIZE, DIGEST_LEN)
INNER_PUBLIC_MEMORY_LOG_SIZE = INNER_PUBLIC_MEMORY_LOG_SIZE_PLACEHOLDER


def recursion(inner_public_memory, proof_transcript, bytecode_value_hint):
    fs: Mut = fs_new(proof_transcript)

    # table dims
    debug_assert(N_TABLES + 1 < DIGEST_LEN)
    fs, dims = fs_receive_chunks(fs, 1)
    for i in unroll(N_TABLES + 2, 8):
        assert dims[i] == 0
    whir_log_inv_rate = dims[0]
    log_memory = dims[1]
    table_log_heights = dims + 2

    assert MIN_WHIR_LOG_INV_RATE <= whir_log_inv_rate
    assert whir_log_inv_rate <= MAX_WHIR_LOG_INV_RATE

    log_n_cycles = table_log_heights[EXECUTION_TABLE_INDEX]
    assert log_n_cycles <= log_memory

    log_bytecode_padded = maximum(LOG_GUEST_BYTECODE_LEN, log_n_cycles)

    table_heights = Array(N_TABLES)
    for i in unroll(0, N_TABLES):
        table_log_height = table_log_heights[i]
        table_heights[i] = powers_of_two(table_log_height)
        assert table_log_height <= log_n_cycles
        assert MIN_LOG_N_ROWS_PER_TABLE <= table_log_height
        assert table_log_height <= MAX_LOG_N_ROWS_PER_TABLE[i]
    assert MIN_LOG_MEMORY_SIZE <= log_memory
    assert log_memory <= MAX_LOG_MEMORY_SIZE
    assert LOG_GUEST_BYTECODE_LEN <= log_memory

    stacked_n_vars = compute_stacked_n_vars(log_memory, log_bytecode_padded, table_heights)
    assert stacked_n_vars <= TWO_ADICITY + WHIR_INITIAL_FOLDING_FACTOR - whir_log_inv_rate

    num_oods = get_num_oods(whir_log_inv_rate, stacked_n_vars)
    num_ood_at_commitment = num_oods[0]
    fs, whir_base_root, whir_base_ood_points, whir_base_ood_evals = parse_commitment(fs, num_ood_at_commitment)

    fs, logup_c = fs_sample_ef(fs)

    fs, logup_alphas = fs_sample_many_ef(fs, log2_ceil(MAX_BUS_WIDTH))

    logup_alphas_eq_poly = poly_eq_extension(logup_alphas, log2_ceil(MAX_BUS_WIDTH))

    # GENERIC LOGUP

    n_vars_logup_gkr = compute_total_gkr_n_vars(log_memory, log_bytecode_padded, table_heights)

    fs, quotient_gkr, point_gkr, numerators_value, denominators_value = verify_gkr_quotient(fs, n_vars_logup_gkr)
    set_to_5_zeros(quotient_gkr)

    memory_and_acc_prefix = multilinear_location_prefix(0, n_vars_logup_gkr - log_memory, point_gkr)

    fs, value_acc = fs_receive_ef_inlined(fs, 1)
    fs, value_memory = fs_receive_ef_inlined(fs, 1)

    retrieved_numerators_value: Mut = opposite_extension_ret(mul_extension_ret(memory_and_acc_prefix, value_acc))

    value_index = mle_of_01234567_etc(point_gkr + (n_vars_logup_gkr - log_memory) * DIM, log_memory)
    fingerprint_memory = fingerprint_2(LOGUP_MEMORY_DOMAINSEP, value_memory, value_index, logup_alphas_eq_poly)
    retrieved_denominators_value: Mut = mul_extension_ret(
        memory_and_acc_prefix, sub_extension_ret(logup_c, fingerprint_memory)
    )

    offset: Mut = powers_of_two(log_memory)

    bytecode_and_acc_point = point_gkr + (n_vars_logup_gkr - LOG_GUEST_BYTECODE_LEN) * DIM
    bytecode_multilinear_location_prefix = multilinear_location_prefix(
        offset / 2 ** LOG_GUEST_BYTECODE_LEN, n_vars_logup_gkr - LOG_GUEST_BYTECODE_LEN, point_gkr
    )
    bytecode_padded_multilinear_location_prefix = multilinear_location_prefix(
        offset / powers_of_two(log_bytecode_padded), n_vars_logup_gkr - log_bytecode_padded, point_gkr
    )
    # Build padded claim data: [point | value | zero padding]
    bytecode_claim = Array(BYTECODE_CLAIM_SIZE_PADDED)
    copy_many_ef(bytecode_and_acc_point, bytecode_claim, LOG_GUEST_BYTECODE_LEN)
    copy_many_ef(
        logup_alphas + (log2_ceil(MAX_BUS_WIDTH) - log2_ceil(N_INSTRUCTION_COLUMNS)) * DIM,
        bytecode_claim + LOG_GUEST_BYTECODE_LEN * DIM,
        log2_ceil(N_INSTRUCTION_COLUMNS),
    )
    copy_5(bytecode_value_hint, bytecode_claim + BYTECODE_POINT_N_VARS * DIM)
    for k in unroll(BYTECODE_CLAIM_SIZE, BYTECODE_CLAIM_SIZE_PADDED):
        bytecode_claim[k] = 0
    bytecode_value = bytecode_claim + BYTECODE_POINT_N_VARS * DIM
    bytecode_value_corrected: Mut = bytecode_value
    for i in unroll(0, log2_ceil(MAX_BUS_WIDTH) - log2_ceil(N_INSTRUCTION_COLUMNS)):
        bytecode_value_corrected = mul_extension_ret(
            bytecode_value_corrected, one_minus_self_extension_ret(logup_alphas + i * DIM)
        )

    fs, value_bytecode_acc = fs_receive_ef_inlined(fs, 1)
    retrieved_numerators_value = sub_extension_ret(
        retrieved_numerators_value, mul_extension_ret(bytecode_multilinear_location_prefix, value_bytecode_acc)
    )

    bytecode_index_value = mle_of_01234567_etc(bytecode_and_acc_point, LOG_GUEST_BYTECODE_LEN)
    retrieved_denominators_value = add_extension_ret(
        retrieved_denominators_value,
        mul_extension_ret(
            bytecode_multilinear_location_prefix,
            sub_extension_ret(
                logup_c,
                add_extension_ret(
                    bytecode_value_corrected,
                    add_extension_ret(
                        mul_extension_ret(bytecode_index_value, logup_alphas_eq_poly + N_INSTRUCTION_COLUMNS * DIM),
                        mul_base_extension_ret(
                            LOGUP_BYTECODE_DOMAINSEP, logup_alphas_eq_poly + (2 ** log2_ceil(MAX_BUS_WIDTH) - 1) * DIM
                        ),
                    ),
                ),
            ),
        ),
    )
    retrieved_denominators_value = add_extension_ret(
        retrieved_denominators_value,
        mul_extension_ret(
            bytecode_padded_multilinear_location_prefix,
            mle_of_zeros_then_ones(
                point_gkr + (n_vars_logup_gkr - log_bytecode_padded) * DIM,
                2 ** LOG_GUEST_BYTECODE_LEN,
                log_bytecode_padded,
            ),
        ),
    )
    offset += powers_of_two(log_bytecode_padded)

    # Dispatch based on table height ordering (sorted by descending height)
    if maximum(table_log_heights[1], table_log_heights[2]) == table_log_heights[1]:
        continue_recursion_ordered(1, 2, fs, offset, retrieved_numerators_value, retrieved_denominators_value, table_heights, table_log_heights, point_gkr, n_vars_logup_gkr, logup_alphas_eq_poly, logup_c, numerators_value, denominators_value, log_memory, inner_public_memory, stacked_n_vars, whir_log_inv_rate, whir_base_root, whir_base_ood_points, whir_base_ood_evals, num_ood_at_commitment, log_n_cycles, log_bytecode_padded, bytecode_and_acc_point, value_memory, value_acc, value_bytecode_acc)
    else:
        continue_recursion_ordered(2, 1, fs, offset, retrieved_numerators_value, retrieved_denominators_value, table_heights, table_log_heights, point_gkr, n_vars_logup_gkr, logup_alphas_eq_poly, logup_c, numerators_value, denominators_value, log_memory, inner_public_memory, stacked_n_vars, whir_log_inv_rate, whir_base_root, whir_base_ood_points, whir_base_ood_evals, num_ood_at_commitment, log_n_cycles, log_bytecode_padded, bytecode_and_acc_point, value_memory, value_acc, value_bytecode_acc)

    return bytecode_claim


@inline
def continue_recursion_ordered(second_table, third_table, fs, offset, retrieved_numerators_value, retrieved_denominators_value, table_heights, table_log_heights, point_gkr, n_vars_logup_gkr, logup_alphas_eq_poly, logup_c, numerators_value, denominators_value, log_memory, inner_public_memory, stacked_n_vars, whir_log_inv_rate, whir_base_root, whir_base_ood_points, whir_base_ood_evals, num_ood_at_commitment, log_n_cycles, log_bytecode_padded, bytecode_and_acc_point, value_memory, value_acc, value_bytecode_acc):
    bus_numerators_values = DynArray([])
    bus_denominators_values = DynArray([])
    pcs_points = DynArray([])  # [[_; N]; N_TABLES]
    for i in unroll(0, N_TABLES):
        pcs_points.push(DynArray([]))
    pcs_values = DynArray([])  # [[[[] or [_]; num cols]; N]; N_TABLES]
    for i in unroll(0, N_TABLES):
        pcs_values.push(DynArray([]))
        pcs_values[i].push(DynArray([]))
        total_num_cols_for_logup = NUM_COLS_TOTAL[i]
        for _ in unroll(0, total_num_cols_for_logup):
            pcs_values[i][0].push(DynArray([]))

    for sorted_pos in unroll(0, N_TABLES):
        table_index: Imu
        if sorted_pos == 0:
            table_index = EXECUTION_TABLE_INDEX
        if sorted_pos == 1:
            table_index = second_table
        if sorted_pos == 2:
            table_index = third_table
        # I] Bus (data flow between tables)

        log_n_rows = table_log_heights[table_index]
        n_rows = table_heights[table_index]
        inner_point = point_gkr + (n_vars_logup_gkr - log_n_rows) * DIM
        pcs_points[table_index].push(inner_point)

        if table_index == EXECUTION_TABLE_INDEX:
            # 0] Bytecode lookup
            bytecode_prefix = multilinear_location_prefix(offset / n_rows, n_vars_logup_gkr - log_n_rows, point_gkr)

            fs, eval_on_pc = fs_receive_ef_inlined(fs, 1)
            pcs_values[EXECUTION_TABLE_INDEX][0][COL_PC].push(eval_on_pc)
            fs, instr_evals = fs_receive_ef_inlined(fs, N_INSTRUCTION_COLUMNS)
            for i in unroll(0, N_INSTRUCTION_COLUMNS):
                global_index = N_COMMITTED_EXEC_COLUMNS + i
                pcs_values[EXECUTION_TABLE_INDEX][0][global_index].push(instr_evals + i * DIM)
            retrieved_numerators_value = add_extension_ret(retrieved_numerators_value, bytecode_prefix)
            fingerp = fingerprint_bytecode(instr_evals, eval_on_pc, logup_alphas_eq_poly)
            retrieved_denominators_value = add_extension_ret(
                retrieved_denominators_value,
                mul_extension_ret(bytecode_prefix, sub_extension_ret(logup_c, fingerp)),
            )
            offset += n_rows

        prefix = multilinear_location_prefix(offset / n_rows, n_vars_logup_gkr - log_n_rows, point_gkr)

        fs, eval_on_selector = fs_receive_ef_inlined(fs, 1)
        retrieved_numerators_value = add_extension_ret(
            retrieved_numerators_value, mul_extension_ret(prefix, eval_on_selector)
        )

        fs, eval_on_data = fs_receive_ef_inlined(fs, 1)
        retrieved_denominators_value = add_extension_ret(
            retrieved_denominators_value, mul_extension_ret(prefix, eval_on_data)
        )

        bus_numerators_values.push(eval_on_selector)

        bus_denominators_values.push(eval_on_data)

        offset += n_rows

        # II] Lookup into memory

        for lookup_f_index in unroll(0, len(LOOKUPS_INDEXES[table_index])):
            col_index = LOOKUPS_INDEXES[table_index][lookup_f_index]
            fs, index_eval = fs_receive_ef_inlined(fs, 1)
            debug_assert(len(pcs_values[table_index][0][col_index]) == 0)
            pcs_values[table_index][0][col_index].push(index_eval)
            for i in unroll(0, len(LOOKUPS_VALUES[table_index][lookup_f_index])):
                fs, value_eval = fs_receive_ef_inlined(fs, 1)
                col_index = LOOKUPS_VALUES[table_index][lookup_f_index][i]
                debug_assert(len(pcs_values[table_index][0][col_index]) == 0)
                pcs_values[table_index][0][col_index].push(value_eval)

                pref = multilinear_location_prefix(
                    offset / n_rows, n_vars_logup_gkr - log_n_rows, point_gkr
                )  # TODO there is some duplication here
                retrieved_numerators_value = add_extension_ret(retrieved_numerators_value, pref)
                fingerp = fingerprint_2(
                    LOGUP_MEMORY_DOMAINSEP,
                    value_eval,
                    add_base_extension_ret(i, index_eval),
                    logup_alphas_eq_poly,
                )
                retrieved_denominators_value = add_extension_ret(
                    retrieved_denominators_value,
                    mul_extension_ret(pref, sub_extension_ret(logup_c, fingerp)),
                )

                offset += n_rows

    retrieved_denominators_value = add_extension_ret(
        retrieved_denominators_value,
        mle_of_zeros_then_ones(point_gkr, offset, n_vars_logup_gkr),
    )

    copy_5(retrieved_numerators_value, numerators_value)
    copy_5(retrieved_denominators_value, denominators_value)

    memory_and_acc_point = point_gkr + (n_vars_logup_gkr - log_memory) * DIM

    # END OF GENERIC LOGUP

    # VERIFY BUS AND AIR

    fs, bus_beta = fs_sample_ef(fs)
    fs, air_alpha = fs_sample_ef(fs)
    air_alpha_powers = powers_const(air_alpha, MAX_NUM_AIR_CONSTRAINTS + 1)

    for sorted_pos in unroll(0, N_TABLES):
        table_index: Imu
        if sorted_pos == 0:
            table_index = EXECUTION_TABLE_INDEX
        if sorted_pos == 1:
            table_index = second_table
        if sorted_pos == 2:
            table_index = third_table
        log_n_rows = table_log_heights[table_index]
        bus_numerator_value = bus_numerators_values[sorted_pos]
        bus_denominator_value = bus_denominators_values[sorted_pos]
        total_num_cols = NUM_COLS_AIR[table_index]

        bus_final_value: Mut = bus_numerator_value
        if table_index != EXECUTION_TABLE_INDEX:
            bus_final_value = opposite_extension_ret(bus_final_value)
        bus_final_value = add_extension_ret(
            bus_final_value,
            mul_extension_ret(bus_beta, sub_extension_ret(bus_denominator_value, logup_c)),
        )

        zerocheck_challenges = pcs_points[table_index][0]

        fs, outer_point, outer_eval = sumcheck_verify(fs, log_n_rows, bus_final_value, AIR_DEGREES[table_index] + 1)

        n_up_columns = N_AIR_COLUMNS[table_index]
        n_down_columns = len(AIR_DOWN_COLUMNS[table_index])
        fs, inner_evals = fs_receive_ef_inlined(fs, n_up_columns + n_down_columns)

        air_constraints_eval = evaluate_air_constraints(
            table_index, inner_evals, air_alpha_powers, bus_beta, logup_alphas_eq_poly
        )
        expected_outer_eval = mul_extension_ret(
            air_constraints_eval,
            eq_mle_extension(zerocheck_challenges, outer_point, log_n_rows),
        )
        copy_5(expected_outer_eval, outer_eval)

        if len(AIR_DOWN_COLUMNS[table_index]) != 0:
            fs, batching_scalar = fs_sample_ef(fs)
            batching_scalar_powers = powers_const(batching_scalar, n_down_columns)
            evals_down = inner_evals + n_up_columns * DIM
            inner_sum: Mut = dot_product_ee_ret(evals_down, batching_scalar_powers, n_down_columns)

            fs, inner_point, inner_value = sumcheck_verify(fs, log_n_rows, inner_sum, 2)

            matrix_down_sc_eval = next_mle(outer_point, inner_point, log_n_rows)

            fs, evals_f_on_down_columns = fs_receive_ef_inlined(fs, n_down_columns)
            batched_col_down_sc_eval: Mut = dot_product_ee_ret(
                evals_f_on_down_columns, batching_scalar_powers, n_down_columns
            )

            copy_5(
                inner_value,
                mul_extension_ret(batched_col_down_sc_eval, matrix_down_sc_eval),
            )

            pcs_points[table_index].push(inner_point)
            pcs_values[table_index].push(DynArray([]))
            last_index = len(pcs_values[table_index]) - 1
            for _ in unroll(0, total_num_cols):
                pcs_values[table_index][last_index].push(DynArray([]))
            for i in unroll(0, n_down_columns):
                pcs_values[table_index][last_index][AIR_DOWN_COLUMNS[table_index][i]].push(
                    evals_f_on_down_columns + i * DIM
                )

        pcs_points[table_index].push(outer_point)
        pcs_values[table_index].push(DynArray([]))
        last_index_2 = len(pcs_values[table_index]) - 1
        for _ in unroll(0, total_num_cols):
            pcs_values[table_index][last_index_2].push(DynArray([]))
        for i in unroll(0, n_up_columns):
            pcs_values[table_index][last_index_2][i].push(inner_evals + i * DIM)

    fs, public_memory_random_point = fs_sample_many_ef(fs, INNER_PUBLIC_MEMORY_LOG_SIZE)
    poly_eq_public_mem = poly_eq_extension(public_memory_random_point, INNER_PUBLIC_MEMORY_LOG_SIZE)
    public_memory_eval = Array(DIM)
    dot_product_be_const(inner_public_memory, poly_eq_public_mem, public_memory_eval, 2**INNER_PUBLIC_MEMORY_LOG_SIZE)

    # WHIR BASE
    combination_randomness_gen: Mut
    fs, combination_randomness_gen = fs_sample_ef(fs)
    combination_randomness_powers: Mut = powers(
        combination_randomness_gen, num_ood_at_commitment + TOTAL_WHIR_STATEMENTS
    )
    whir_sum: Mut = Array(DIM)
    dot_product_ee_dynamic(whir_base_ood_evals, combination_randomness_powers, whir_sum, num_ood_at_commitment)
    curr_randomness: Mut = combination_randomness_powers + num_ood_at_commitment * DIM

    whir_sum = add_extension_ret(mul_extension_ret(value_memory, curr_randomness), whir_sum)
    curr_randomness += DIM
    whir_sum = add_extension_ret(mul_extension_ret(value_acc, curr_randomness), whir_sum)
    curr_randomness += DIM
    whir_sum = add_extension_ret(mul_extension_ret(public_memory_eval, curr_randomness), whir_sum)
    curr_randomness += DIM
    whir_sum = add_extension_ret(mul_extension_ret(value_bytecode_acc, curr_randomness), whir_sum)
    curr_randomness += DIM

    whir_sum = add_extension_ret(mul_extension_ret(embed_in_ef(STARTING_PC), curr_randomness), whir_sum)
    curr_randomness += DIM
    whir_sum = add_extension_ret(mul_extension_ret(embed_in_ef(ENDING_PC), curr_randomness), whir_sum)
    curr_randomness += DIM

    for sorted_pos in unroll(0, N_TABLES):
        table_index: Imu
        if sorted_pos == 0:
            table_index = EXECUTION_TABLE_INDEX
        if sorted_pos == 1:
            table_index = second_table
        if sorted_pos == 2:
            table_index = third_table
        debug_assert(len(pcs_points[table_index]) == len(pcs_values[table_index]))
        for i in unroll(0, len(pcs_values[table_index])):
            for j in unroll(0, len(pcs_values[table_index][i])):
                debug_assert(len(pcs_values[table_index][i][j]) < 2)
                if len(pcs_values[table_index][i][j]) == 1:
                    whir_sum = add_extension_ret(
                        mul_extension_ret(pcs_values[table_index][i][j][0], curr_randomness),
                        whir_sum,
                    )
                    curr_randomness += DIM

    folding_randomness_global: Mut
    s: Mut
    final_value: Mut
    end_sum: Mut
    fs, folding_randomness_global, s, final_value, end_sum = whir_open(
        fs,
        stacked_n_vars,
        whir_log_inv_rate,
        whir_base_root,
        whir_base_ood_points,
        combination_randomness_powers,
        whir_sum,
    )

    curr_randomness = combination_randomness_powers + num_ood_at_commitment * DIM

    eq_memory_and_acc_point = eq_mle_extension(
        folding_randomness_global + (stacked_n_vars - log_memory) * DIM,
        memory_and_acc_point,
        log_memory,
    )
    prefix_memory = multilinear_location_prefix(0, stacked_n_vars - log_memory, folding_randomness_global)
    s = add_extension_ret(
        s,
        mul_extension_ret(mul_extension_ret(curr_randomness, prefix_memory), eq_memory_and_acc_point),
    )
    curr_randomness += DIM

    prefix_acc_memory = multilinear_location_prefix(1, stacked_n_vars - log_memory, folding_randomness_global)
    s = add_extension_ret(
        s,
        mul_extension_ret(mul_extension_ret(curr_randomness, prefix_acc_memory), eq_memory_and_acc_point),
    )
    curr_randomness += DIM

    eq_pub_mem = eq_mle_extension(
        folding_randomness_global + (stacked_n_vars - INNER_PUBLIC_MEMORY_LOG_SIZE) * DIM,
        public_memory_random_point,
        INNER_PUBLIC_MEMORY_LOG_SIZE,
    )
    prefix_pub_mem = multilinear_location_prefix(
        0, stacked_n_vars - INNER_PUBLIC_MEMORY_LOG_SIZE, folding_randomness_global
    )
    s = add_extension_ret(
        s,
        mul_extension_ret(mul_extension_ret(curr_randomness, prefix_pub_mem), eq_pub_mem),
    )
    curr_randomness += DIM

    offset = powers_of_two(log_memory) * 2  # memory and acc_memory

    eq_bytecode_acc = eq_mle_extension(
        folding_randomness_global + (stacked_n_vars - LOG_GUEST_BYTECODE_LEN) * DIM,
        bytecode_and_acc_point,
        LOG_GUEST_BYTECODE_LEN,
    )
    prefix_bytecode_acc = multilinear_location_prefix(
        offset / 2 ** LOG_GUEST_BYTECODE_LEN,
        stacked_n_vars - LOG_GUEST_BYTECODE_LEN,
        folding_randomness_global,
    )
    s = add_extension_ret(
        s,
        mul_extension_ret(mul_extension_ret(curr_randomness, prefix_bytecode_acc), eq_bytecode_acc),
    )
    curr_randomness += DIM
    offset += powers_of_two(log_bytecode_padded)

    prefix_pc_start = multilinear_location_prefix(
        offset + COL_PC * powers_of_two(log_n_cycles),
        stacked_n_vars,
        folding_randomness_global,
    )
    s = add_extension_ret(s, mul_extension_ret(curr_randomness, prefix_pc_start))
    curr_randomness += DIM

    prefix_pc_end = multilinear_location_prefix(
        offset + (COL_PC + 1) * powers_of_two(log_n_cycles) - 1,
        stacked_n_vars,
        folding_randomness_global,
    )
    s = add_extension_ret(s, mul_extension_ret(curr_randomness, prefix_pc_end))
    curr_randomness += DIM

    for sorted_pos in unroll(0, N_TABLES):
        table_index: Imu
        if sorted_pos == 0:
            table_index = EXECUTION_TABLE_INDEX
        if sorted_pos == 1:
            table_index = second_table
        if sorted_pos == 2:
            table_index = third_table
        log_n_rows = table_log_heights[table_index]
        n_rows = table_heights[table_index]
        total_num_cols = NUM_COLS_AIR[table_index]
        for i in unroll(0, len(pcs_points[table_index])):
            point = pcs_points[table_index][i]
            eq_factor = eq_mle_extension(
                point,
                folding_randomness_global + (stacked_n_vars - log_n_rows) * DIM,
                log_n_rows,
            )
            for j in unroll(0, total_num_cols):
                if len(pcs_values[table_index][i][j]) == 1:
                    prefix = multilinear_location_prefix(
                        offset / n_rows + j,
                        stacked_n_vars - log_n_rows,
                        folding_randomness_global,
                    )
                    s = add_extension_ret(
                        s,
                        mul_extension_ret(mul_extension_ret(curr_randomness, prefix), eq_factor),
                    )
                    curr_randomness += DIM
        offset += n_rows * total_num_cols

    copy_5(mul_extension_ret(s, final_value), end_sum)
    return


def multilinear_location_prefix(offset, n_vars, point):
    bits = checked_decompose_bits_small_value(offset, n_vars)
    res = eq_mle_base_extension(bits, point, n_vars)
    return res


def fingerprint_2(table_index, data_1, data_2, logup_alphas_eq_poly):
    buff = Array(DIM * 2)
    copy_5(data_1, buff)
    copy_5(data_2, buff + DIM)
    res: Mut = dot_product_ee_ret(buff, logup_alphas_eq_poly, 2)
    res = add_extension_ret(
        res, mul_base_extension_ret(table_index, logup_alphas_eq_poly + (2 ** log2_ceil(MAX_BUS_WIDTH) - 1) * DIM)
    )
    return res


def fingerprint_bytecode(instr_evals, eval_on_pc, logup_alphas_eq_poly):
    res: Mut = dot_product_ee_ret(instr_evals, logup_alphas_eq_poly, N_INSTRUCTION_COLUMNS)
    res = add_extension_ret(res, mul_extension_ret(eval_on_pc, logup_alphas_eq_poly + N_INSTRUCTION_COLUMNS * DIM))
    res = add_extension_ret(
        res,
        mul_base_extension_ret(LOGUP_BYTECODE_DOMAINSEP, logup_alphas_eq_poly + (2 ** log2_ceil(MAX_BUS_WIDTH) - 1) * DIM),
    )
    return res


def verify_gkr_quotient(fs: Mut, n_vars):
    fs, nums = fs_receive_ef_inlined(fs, 2)
    fs, denoms = fs_receive_ef_inlined(fs, 2)

    q1 = div_extension_ret(nums, denoms)
    q2 = div_extension_ret(nums + DIM, denoms + DIM)
    quotient = add_extension_ret(q1, q2)

    points = Array(n_vars)
    claims_num = Array(n_vars)
    claims_den = Array(n_vars)

    fs, points[0] = fs_sample_ef(fs)

    point_poly_eq = poly_eq_extension(points[0], 1)

    first_claim_num = dot_product_ee_ret(nums, point_poly_eq, 2)
    first_claim_den = dot_product_ee_ret(denoms, point_poly_eq, 2)
    claims_num[0] = first_claim_num
    claims_den[0] = first_claim_den

    for i in range(1, n_vars):
        fs, points[i], claims_num[i], claims_den[i] = verify_gkr_quotient_step(
            fs, i, points[i - 1], claims_num[i - 1], claims_den[i - 1]
        )

    return (
        fs,
        quotient,
        points[n_vars - 1],
        claims_num[n_vars - 1],
        claims_den[n_vars - 1],
    )


def verify_gkr_quotient_step(fs: Mut, n_vars, point, claim_num, claim_den):
    fs, alpha = fs_sample_ef(fs)
    alpha_mul_claim_den = mul_extension_ret(alpha, claim_den)
    num_plus_alpha_mul_claim_den = add_extension_ret(claim_num, alpha_mul_claim_den)
    postponed_point = Array((n_vars + 1) * DIM)
    fs, postponed_value = sumcheck_verify_helper(fs, n_vars, num_plus_alpha_mul_claim_den, 3, postponed_point + DIM)
    fs, inner_evals = fs_receive_ef_inlined(fs, 4)
    a_num = inner_evals
    b_num = inner_evals + DIM
    a_den = inner_evals + 2 * DIM
    b_den = inner_evals + 3 * DIM
    sum_num, sum_den = sum_2_ef_fractions(a_num, a_den, b_num, b_den)
    sum_den_mul_alpha = mul_extension_ret(sum_den, alpha)
    sum_num_plus_sum_den_mul_alpha = add_extension_ret(sum_num, sum_den_mul_alpha)
    eq_factor = eq_mle_extension(point, postponed_point + DIM, n_vars)
    mul_extension(sum_num_plus_sum_den_mul_alpha, eq_factor, postponed_value)

    fs, beta = fs_sample_ef(fs)

    point_poly_eq = poly_eq_extension(beta, 1)
    new_claim_num = dot_product_ee_ret(inner_evals, point_poly_eq, 2)
    new_claim_den = dot_product_ee_ret(inner_evals + 2 * DIM, point_poly_eq, 2)

    copy_5(beta, postponed_point)

    return fs, postponed_point, new_claim_num, new_claim_den


@inline
def compute_stacked_n_vars(log_memory, log_bytecode_padded, tables_heights):
    total: Mut = powers_of_two(log_memory + 1) # memory + acc_memory
    total += powers_of_two(log_bytecode_padded)
    for table_index in unroll(0, N_TABLES):
        n_rows = tables_heights[table_index]
        total += n_rows * NUM_COLS_AIR[table_index]
    debug_assert(30 - 24 < MIN_LOG_N_ROWS_PER_TABLE) # cf log2_ceil
    return MIN_LOG_N_ROWS_PER_TABLE + log2_ceil_runtime(total / 2**MIN_LOG_N_ROWS_PER_TABLE)

def compute_total_gkr_n_vars(log_memory, log_bytecode_padded, tables_heights):
    total: Mut = powers_of_two(log_memory)
    total += powers_of_two(log_bytecode_padded)
    total += tables_heights[EXECUTION_TABLE_INDEX]
    for table_index in unroll(0, N_TABLES):
        n_rows = tables_heights[table_index]
        total_lookup_values: Mut = 0
        for i in unroll(0, len(LOOKUPS_INDEXES[table_index])):
            total_lookup_values += len(LOOKUPS_VALUES[table_index][i])
        total_lookup_values += 1 # for the bus
        total += n_rows * total_lookup_values
    return log2_ceil_runtime(total)

def evaluate_air_constraints(table_index, inner_evals, air_alpha_powers, bus_beta, logup_alphas_eq_poly):
    res: Imu
    debug_assert(table_index < 3)
    match table_index:
        case 0:
            res = evaluate_air_constraints_table_0(inner_evals, air_alpha_powers, bus_beta, logup_alphas_eq_poly)
        case 1:
            res = evaluate_air_constraints_table_1(inner_evals, air_alpha_powers, bus_beta, logup_alphas_eq_poly)
        case 2:
            res = evaluate_air_constraints_table_2(inner_evals, air_alpha_powers, bus_beta, logup_alphas_eq_poly)
    return res
    

EVALUATE_AIR_FUNCTIONS_PLACEHOLDER
