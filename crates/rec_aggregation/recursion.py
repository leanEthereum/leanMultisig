from snark_lib import *
from whir import *

N_TABLES = N_TABLES_PLACEHOLDER
MIN_LOG_N_ROWS_PER_TABLE = MIN_LOG_N_ROWS_PER_TABLE_PLACEHOLDER
MAX_LOG_N_ROWS_PER_TABLE = MAX_LOG_N_ROWS_PER_TABLE_PLACEHOLDER
MIN_LOG_MEMORY_SIZE = MIN_LOG_MEMORY_SIZE_PLACEHOLDER
MAX_LOG_MEMORY_SIZE = MAX_LOG_MEMORY_SIZE_PLACEHOLDER
N_VARS_LOGUP_GKR = N_VARS_LOGUP_GKR_PLACEHOLDER
MAX_BUS_WIDTH = MAX_BUS_WIDTH_PLACEHOLDER
MAX_NUM_AIR_CONSTRAINTS = MAX_NUM_AIR_CONSTRAINTS_PLACEHOLDER

MEMORY_TABLE_INDEX = MEMORY_TABLE_INDEX_PLACEHOLDER
BYTECODE_TABLE_INDEX = BYTECODE_TABLE_INDEX_PLACEHOLDER
EXECUTION_TABLE_INDEX = EXECUTION_TABLE_INDEX_PLACEHOLDER

LOOKUPS_F_INDEXES = LOOKUPS_F_INDEXES_PLACEHOLDER  # [[_; ?]; N_TABLES]
LOOKUPS_F_VALUES = LOOKUPS_F_VALUES_PLACEHOLDER  # [[[_; ?]; ?]; N_TABLES]

LOOKUPS_EF_INDEXES = LOOKUPS_EF_INDEXES_PLACEHOLDER  # [[_; ?]; N_TABLES]
LOOKUPS_EF_VALUES = LOOKUPS_EF_VALUES_PLACEHOLDER  # [[_; ?]; N_TABLES]

NUM_COLS_F_AIR = NUM_COLS_F_AIR_PLACEHOLDER
NUM_COLS_EF_AIR = NUM_COLS_EF_AIR_PLACEHOLDER

NUM_COLS_F_COMMITTED = NUM_COLS_F_COMMITTED_PLACEHOLDER

AIR_DEGREES = AIR_DEGREES_PLACEHOLDER  # [_; N_TABLES]
N_AIR_COLUMNS_F = N_AIR_COLUMNS_F_PLACEHOLDER  # [_; N_TABLES]
N_AIR_COLUMNS_EF = N_AIR_COLUMNS_EF_PLACEHOLDER  # [_; N_TABLES]
AIR_DOWN_COLUMNS_F = AIR_DOWN_COLUMNS_F_PLACEHOLDER  # [[_; ?]; N_TABLES]
AIR_DOWN_COLUMNS_EF = AIR_DOWN_COLUMNS_EF_PLACEHOLDER  # [[_; _]; N_TABLES]

N_INSTRUCTION_COLUMNS = N_INSTRUCTION_COLUMNS_PLACEHOLDER
N_COMMITTED_EXEC_COLUMNS = N_COMMITTED_EXEC_COLUMNS_PLACEHOLDER

GUEST_BYTECODE_LEN = GUEST_BYTECODE_LEN_PLACEHOLDER
COL_PC = COL_PC_PLACEHOLDER
TOTAL_WHIR_STATEMENTS = TOTAL_WHIR_STATEMENTS_PLACEHOLDER
STARTING_PC = STARTING_PC_PLACEHOLDER
ENDING_PC = ENDING_PC_PLACEHOLDER
NONRESERVED_PROGRAM_INPUT_START = NONRESERVED_PROGRAM_INPUT_START_PLACEHOLDER


def main():
    mem = 0
    priv_start = mem[PRIVATE_INPUT_START_PTR]
    proof_size = priv_start[0]
    outer_public_memory_log_size = priv_start[1]
    outer_public_memory_size = powers_of_two(outer_public_memory_log_size)
    n_recursions = priv_start[2]
    outer_public_memory = priv_start + 3
    proofs_start = outer_public_memory + outer_public_memory_size
    for i in range(0, n_recursions):
        proof_transcript = proofs_start + i * proof_size
        recursion(outer_public_memory_log_size, outer_public_memory, proof_transcript)
    return


def recursion(outer_public_memory_log_size, outer_public_memory, proof_transcript):
    fs: Mut = fs_new(proof_transcript)

    # table dims
    debug_assert(N_TABLES + 1 < VECTOR_LEN)  # (because duplex only once bellow)
    fs, mem_and_table_dims = fs_receive_chunks(fs, 1)
    for i in unroll(N_TABLES + 1, 8):
        assert mem_and_table_dims[i] == 0
    log_memory = mem_and_table_dims[0]
    table_dims = mem_and_table_dims + 1

    for i in unroll(0, N_TABLES):
        n_vars_for_table = table_dims[i]
        assert n_vars_for_table <= log_memory
        assert MIN_LOG_N_ROWS_PER_TABLE <= n_vars_for_table
        assert n_vars_for_table <= MAX_LOG_N_ROWS_PER_TABLE[i]
    assert MIN_LOG_MEMORY_SIZE <= log_memory
    assert log_memory <= MAX_LOG_MEMORY_SIZE
    assert log_memory <= GUEST_BYTECODE_LEN

    fs, whir_base_root, whir_base_ood_points, whir_base_ood_evals = parse_whir_commitment_const(fs, WHIR_NUM_OOD_COMMIT)

    logup_c = fs_sample_ef(fs)
    fs = duplexing(fs)

    logup_alphas = Array(DIM * log2_ceil(MAX_BUS_WIDTH))
    for i in unroll(0, log2_ceil(MAX_BUS_WIDTH)):
        copy_5(fs_sample_ef(fs), logup_alphas + i * DIM)  # TODO avoid duplication
        fs = duplexing(fs)
    logup_alphas_eq_poly = poly_eq_extension(logup_alphas, log2_ceil(MAX_BUS_WIDTH))
    # GENRIC LOGUP

    fs, quotient_gkr, point_gkr, numerators_value, denominators_value = verify_gkr_quotient(fs, N_VARS_LOGUP_GKR)
    set_to_5_zeros(quotient_gkr)

    memory_and_acc_prefix = multilinear_location_prefix(0, N_VARS_LOGUP_GKR - log_memory, point_gkr)

    fs, value_acc = fs_receive_ef(fs, 1)
    fs, value_memory = fs_receive_ef(fs, 1)

    retrieved_numerators_value: Mut = opposite_extension_ret(mul_extension_ret(memory_and_acc_prefix, value_acc))

    value_index = mle_of_01234567_etc(point_gkr + (N_VARS_LOGUP_GKR - log_memory) * DIM, log_memory)
    fingerprint_memory = fingerprint_2(MEMORY_TABLE_INDEX, value_index, value_memory, logup_alphas_eq_poly)
    retrieved_denominators_value: Mut = mul_extension_ret(
        memory_and_acc_prefix, sub_extension_ret(logup_c, fingerprint_memory)
    )

    offset: Mut = powers_of_two(log_memory)

    log_bytecode = log2_ceil(GUEST_BYTECODE_LEN)
    log_n_cycles = table_dims[EXECUTION_TABLE_INDEX]
    log_bytecode_padded = maximum(log_bytecode, log_n_cycles)
    bytecode_and_acc_point = point_gkr + (N_VARS_LOGUP_GKR - log_bytecode) * DIM
    bytecode_multilinear_location_prefix = multilinear_location_prefix(
        offset / log_bytecode, N_VARS_LOGUP_GKR - log_bytecode, point_gkr
    )
    bytecode_padded_multilinear_location_prefix = multilinear_location_prefix(
        offset / log_bytecode_padded, N_VARS_LOGUP_GKR - log_bytecode_padded, point_gkr
    )
    NONRESERVED_PROGRAM_INPUT_START_ = NONRESERVED_PROGRAM_INPUT_START
    assert NONRESERVED_PROGRAM_INPUT_START_[0] == log_bytecode + log2_ceil(N_INSTRUCTION_COLUMNS)
    copy_many_ef(bytecode_and_acc_point, NONRESERVED_PROGRAM_INPUT_START + 1, log_bytecode)
    copy_many_ef(
        logup_alphas + (log2_ceil(MAX_BUS_WIDTH) - log2_ceil(N_INSTRUCTION_COLUMNS)) * DIM,
        NONRESERVED_PROGRAM_INPUT_START + 1 + log_bytecode * DIM,
        log2_ceil(N_INSTRUCTION_COLUMNS),
    )
    bytecode_value = NONRESERVED_PROGRAM_INPUT_START_ + 1 + log_bytecode * DIM
    bytecode_value_corrected: Mut = bytecode_value
    for i in log2_ceil(MAX_BUS_WIDTH) - log2_ceil(N_INSTRUCTION_COLUMNS):
        bytecode_value_corrected = mul_extension_ret(
            bytecode_value_corrected, one_minus_self_extension_ret(logup_alphas + i * DIM)
        )

    fs, value_bytecode_acc = fs_receive_ef(fs, 1)
    retrieved_numerators_value = sub_extension_ret(
        retrieved_numerators_value, mul_extension_ret(bytecode_multilinear_location_prefix, value_bytecode_acc)
    )

    bytecode_index_value = mle_of_01234567_etc(bytecode_and_acc_point, log_bytecode)
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
                            EXECUTION_TABLE_INDEX, logup_alphas_eq_poly + (2 ** log2_ceil(MAX_BUS_WIDTH) - 1) * DIM
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
                point_gkr + (N_VARS_LOGUP_GKR - log_bytecode_padded) * DIM,
                log2_ceil(GUEST_BYTECODE_LEN),
                log_bytecode_padded,
            ),
        ),
    )

    bus_numerators_values = DynArray([])
    bus_denominators_values = DynArray([])
    pcs_points = DynArray([])  # [[_; N]; N_TABLES]
    for i in unroll(0, N_TABLES):
        pcs_points.push(DynArray([]))
    pcs_values = DynArray([])  # [[[[] or [_]; num cols]; N]; N_TABLES]
    for i in unroll(0, N_TABLES):
        pcs_values.push(DynArray([]))
    for table_index in unroll(0, N_TABLES):
        # I] Bus (data flow between tables)

        log_n_rows = table_dims[table_index]
        n_rows = powers_of_two(log_n_rows)
        inner_point = point_gkr + (N_VARS_LOGUP_GKR - log_n_rows) * DIM
        pcs_points[table_index].push(inner_point)

        prefix = multilinear_location_prefix(offset / n_rows, N_VARS_LOGUP_GKR - log_n_rows, point_gkr)

        fs, eval_on_selector = fs_receive_ef(fs, 1)
        retrieved_numerators_value = add_extension_ret(
            retrieved_numerators_value, mul_extension_ret(prefix, eval_on_selector)
        )

        fs, eval_on_data = fs_receive_ef(fs, 1)
        retrieved_denominators_value = add_extension_ret(
            retrieved_denominators_value, mul_extension_ret(prefix, eval_on_data)
        )

        bus_numerators_values.push(eval_on_selector)

        bus_denominators_values.push(eval_on_data)

        offset += n_rows

        # II] Lookup into memory

        pcs_values[table_index].push(DynArray([]))
        total_num_cols = NUM_COLS_F_AIR[table_index] + DIM * NUM_COLS_EF_AIR[table_index]
        for col in unroll(0, total_num_cols):
            pcs_values[table_index][0].push(DynArray([]))

        for lookup_f_index in unroll(0, len(LOOKUPS_F_INDEXES[table_index])):
            col_index = LOOKUPS_F_INDEXES[table_index][lookup_f_index]
            fs, index_eval = fs_receive_ef(fs, 1)
            debug_assert(len(pcs_values[table_index][0][col_index]) == 0)
            pcs_values[table_index][0][col_index].push(index_eval)
            for i in unroll(0, len(LOOKUPS_F_VALUES[table_index][lookup_f_index])):
                fs, value_eval = fs_receive_ef(fs, 1)
                col_index = LOOKUPS_F_VALUES[table_index][lookup_f_index][i]
                debug_assert(len(pcs_values[table_index][0][col_index]) == 0)
                pcs_values[table_index][0][col_index].push(value_eval)

                pref = multilinear_location_prefix(
                    offset / n_rows, N_VARS_LOGUP_GKR - log_n_rows, point_gkr
                )  # TODO there is some duplication here
                retrieved_numerators_value = add_extension_ret(retrieved_numerators_value, pref)
                fingerp = fingerprint_2(
                    MEMORY_TABLE_INDEX,
                    add_base_extension_ret(i, index_eval),
                    value_eval,
                    logup_alphas_eq_poly,
                )
                retrieved_denominators_value = add_extension_ret(
                    retrieved_denominators_value,
                    mul_extension_ret(pref, sub_extension_ret(logup_c, fingerp)),
                )

                offset += n_rows

        for lookup_ef_index in unroll(0, len(LOOKUPS_EF_INDEXES[table_index])):
            col_index = LOOKUPS_EF_INDEXES[table_index][lookup_ef_index]
            fs, index_eval = fs_receive_ef(fs, 1)
            if len(pcs_values[table_index][0][col_index]) == 0:
                pcs_values[table_index][0][col_index].push(index_eval)
            else:
                # assert equal
                copy_5(index_eval, pcs_values[table_index][0][col_index][0])

            for i in unroll(0, DIM):
                fs, value_eval = fs_receive_ef(fs, 1)
                pref = multilinear_location_prefix(
                    offset / n_rows, N_VARS_LOGUP_GKR - log_n_rows, point_gkr
                )  # TODO there is some duplication here
                retrieved_numerators_value = add_extension_ret(retrieved_numerators_value, pref)
                fingerp = fingerprint_2(
                    MEMORY_TABLE_INDEX,
                    add_base_extension_ret(i, index_eval),
                    value_eval,
                    logup_alphas_eq_poly,
                )
                retrieved_denominators_value = add_extension_ret(
                    retrieved_denominators_value,
                    mul_extension_ret(pref, sub_extension_ret(logup_c, fingerp)),
                )

                global_index = (
                    NUM_COLS_F_COMMITTED[table_index] + LOOKUPS_EF_VALUES[table_index][lookup_ef_index] * DIM + i
                )
                debug_assert(len(pcs_values[table_index][0][global_index]) == 0)
                pcs_values[table_index][0][global_index].push(value_eval)

                offset += n_rows

    retrieved_denominators_value = add_extension_ret(
        retrieved_denominators_value,
        mle_of_zeros_then_ones(point_gkr, offset, N_VARS_LOGUP_GKR),
    )

    copy_5(retrieved_numerators_value, numerators_value)
    copy_5(retrieved_denominators_value, denominators_value)

    memory_and_acc_point = point_gkr + (N_VARS_LOGUP_GKR - log_memory) * DIM

    # END OF GENERIC LOGUP

    # VERIFY BUS AND AIR

    bus_beta = fs_sample_ef(fs)
    fs = duplexing(fs)

    air_alpha = fs_sample_ef(fs)
    air_alpha_powers = powers_const(air_alpha, MAX_NUM_AIR_CONSTRAINTS + 1)

    for table_index in unroll(0, N_TABLES):
        log_n_rows = table_dims[table_index]
        bus_numerator_value = bus_numerators_values[table_index]
        bus_denominator_value = bus_denominators_values[table_index]
        total_num_cols = NUM_COLS_F_AIR[table_index] + DIM * NUM_COLS_EF_AIR[table_index]

        bus_final_value: Mut = bus_numerator_value
        if table_index != EXECUTION_TABLE_INDEX:
            bus_final_value = opposite_extension_ret(bus_final_value)
        bus_final_value = add_extension_ret(
            bus_final_value,
            mul_extension_ret(bus_beta, sub_extension_ret(bus_denominator_value, logup_c)),
        )

        zerocheck_challenges = pcs_points[table_index][0]

        fs, outer_point, outer_eval = sumcheck_verify(fs, log_n_rows, bus_final_value, AIR_DEGREES[table_index] + 1)

        n_up_columns_f = N_AIR_COLUMNS_F[table_index]
        n_up_columns_ef = N_AIR_COLUMNS_EF[table_index]
        n_down_columns_f = len(AIR_DOWN_COLUMNS_F[table_index])
        n_down_columns_ef = len(AIR_DOWN_COLUMNS_EF[table_index])
        n_up_columns = n_up_columns_f + n_up_columns_ef
        n_down_columns = n_down_columns_f + n_down_columns_ef
        fs, inner_evals = fs_receive_ef(fs, n_up_columns + n_down_columns)

        air_constraints_eval = evaluate_air_constraints(
            table_index, inner_evals, air_alpha_powers, bus_beta, logup_alphas_eq_poly
        )
        expected_outer_eval = mul_extension_ret(
            air_constraints_eval,
            eq_mle_extension(zerocheck_challenges, outer_point, log_n_rows),
        )
        copy_5(expected_outer_eval, outer_eval)

        if len(AIR_DOWN_COLUMNS_F[table_index]) != 0:
            batching_scalar = fs_sample_ef(fs)
            batching_scalar_powers = powers_const(batching_scalar, n_down_columns)
            evals_down_f = inner_evals + n_up_columns_f * DIM
            evals_down_ef = inner_evals + (n_up_columns_f + n_down_columns_f + n_up_columns_ef) * DIM
            inner_sum: Mut = dot_product_ret(evals_down_f, batching_scalar_powers, n_down_columns_f, EE)
            if n_down_columns_ef != 0:
                inner_sum = add_extension_ret(
                    inner_sum,
                    dot_product_ret(
                        evals_down_ef,
                        batching_scalar_powers + n_down_columns_f,
                        n_down_columns_ef,
                        EE,
                    ),
                )

            fs, inner_point, inner_value = sumcheck_verify(fs, log_n_rows, inner_sum, 2)

            matrix_down_sc_eval = next_mle(outer_point, inner_point, log_n_rows)

            fs, evals_f_on_down_columns = fs_receive_ef(fs, n_down_columns_f)
            batched_col_down_sc_eval: Mut = dot_product_ret(
                evals_f_on_down_columns, batching_scalar_powers, n_down_columns_f, EE
            )

            evals_ef_on_down_columns: Imu
            if n_down_columns_ef != 0:
                fs, evals_ef_on_down_columns = fs_receive_ef(fs, n_down_columns_ef)
                batched_col_down_sc_eval = add_extension_ret(
                    batched_col_down_sc_eval,
                    dot_product_ret(
                        evals_ef_on_down_columns,
                        batching_scalar_powers + n_down_columns_f,
                        n_down_columns_ef,
                        EE,
                    ),
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
            for i in unroll(0, n_down_columns_f):
                pcs_values[table_index][last_index][AIR_DOWN_COLUMNS_F[table_index][i]].push(
                    evals_f_on_down_columns + i * DIM
                )
            for i in unroll(0, n_down_columns_ef):
                fs, transposed = fs_receive_ef(fs, DIM)
                copy_5(
                    evals_ef_on_down_columns + i * DIM,
                    dot_product_with_the_base_vectors(transposed),
                )
                for j in unroll(0, DIM):
                    virtual_col_index = n_up_columns_f + AIR_DOWN_COLUMNS_EF[table_index][i] * DIM + j
                    pcs_values[table_index][last_index][virtual_col_index].push(transposed + j * DIM)

        pcs_points[table_index].push(outer_point)
        pcs_values[table_index].push(DynArray([]))
        last_index_2 = len(pcs_values[table_index]) - 1
        for _ in unroll(0, total_num_cols):
            pcs_values[table_index][last_index_2].push(DynArray([]))
        for i in unroll(0, n_up_columns_f):
            pcs_values[table_index][last_index_2][i].push(inner_evals + i * DIM)

        for i in unroll(0, n_up_columns_ef):
            fs, transposed = fs_receive_ef(fs, DIM)
            copy_5(
                inner_evals + (n_up_columns_f + n_down_columns_f + i) * DIM,
                dot_product_with_the_base_vectors(transposed),
            )
            for j in unroll(0, DIM):
                virtual_col_index = n_up_columns_f + i * DIM + j
                pcs_values[table_index][last_index_2][virtual_col_index].push(transposed + j * DIM)

    log_num_instrs = log2_ceil(N_INSTRUCTION_COLUMNS)
    bytecode_compression_challenges = Array(DIM * log_num_instrs)
    for i in unroll(0, log_num_instrs):
        copy_5(fs_sample_ef(fs), bytecode_compression_challenges + i * DIM)  # TODO avoid duplication
        if i != log_num_instrs - 1:
            fs = duplexing(fs)

    bytecode_air_values = Array(DIM * 2**log_num_instrs)
    for i in unroll(0, N_INSTRUCTION_COLUMNS):
        col = N_COMMITTED_EXEC_COLUMNS + i
        copy_5(
            pcs_values[EXECUTION_TABLE_INDEX][2][col][0],
            bytecode_air_values + i * DIM,
        )
        pcs_values[EXECUTION_TABLE_INDEX][2][col].pop()
    for i in unroll(N_INSTRUCTION_COLUMNS, 2**log_num_instrs):
        set_to_5_zeros(bytecode_air_values + i * DIM)

    bytecode_air_point = pcs_points[EXECUTION_TABLE_INDEX][2]
    bytecode_lookup_claim = dot_product_ret(
        bytecode_air_values,
        poly_eq_extension(bytecode_compression_challenges, log_num_instrs),
        2**log_num_instrs,
        EE,
    )

    fs, whir_ext_root, whir_ext_ood_points, whir_ext_ood_evals = parse_whir_commitment_const(fs, NUM_OOD_COMMIT_EXT)

    # VERIFY LOGUP*

    log_table_len = log2_ceil(GUEST_BYTECODE_LEN)
    fs, ls_sumcheck_point, ls_sumcheck_value = sumcheck_verify(fs, log_table_len, bytecode_lookup_claim, 2)
    fs, table_eval = fs_receive_ef(fs, 1)
    fs, pushforward_eval = fs_receive_ef(fs, 1)
    mul_extension(table_eval, pushforward_eval, ls_sumcheck_value)

    ls_c = fs_sample_ef(fs)

    fs, quotient_left, claim_point_left, claim_num_left, eval_c_minus_indexes = verify_gkr_quotient(fs, log_n_cycles)
    fs, quotient_right, claim_point_right, pushforward_final_eval, claim_den_right = verify_gkr_quotient(
        fs, log_table_len
    )

    copy_5(quotient_left, quotient_right)

    copy_5(
        eq_mle_extension(claim_point_left, bytecode_air_point, log_n_cycles),
        claim_num_left,
    )
    copy_5(
        sub_extension_ret(ls_c, mle_of_01234567_etc(claim_point_right, log_table_len)),
        claim_den_right,
    )

    # logupstar statements:
    ls_on_indexes_point = claim_point_left
    ls_on_indexes_eval = sub_extension_ret(ls_c, eval_c_minus_indexes)
    ls_on_table_point = ls_sumcheck_point
    ls_on_table_eval = table_eval
    ls_on_pushforward_point_1 = ls_sumcheck_point
    ls_on_pushforward_eval_1 = pushforward_eval
    ls_on_pushforward_point_2 = claim_point_right
    ls_on_pushforward_eval_2 = pushforward_final_eval

    # TODO evaluate the folded bytecode

    pcs_points[EXECUTION_TABLE_INDEX].push(ls_on_indexes_point)
    pcs_values[EXECUTION_TABLE_INDEX].push(DynArray([]))
    last_len = len(pcs_values[EXECUTION_TABLE_INDEX]) - 1
    total_exec_cols = NUM_COLS_F_AIR[EXECUTION_TABLE_INDEX] + DIM * NUM_COLS_EF_AIR[EXECUTION_TABLE_INDEX]
    for _ in unroll(0, total_exec_cols):
        pcs_values[EXECUTION_TABLE_INDEX][last_len].push(DynArray([]))
    pcs_values[EXECUTION_TABLE_INDEX][last_len][COL_PC].push(ls_on_indexes_eval)

    # verify the outer public memory is well constructed (with the conventions)
    for i in unroll(0, next_multiple_of(NONRESERVED_PROGRAM_INPUT_START, DIM) / DIM):
        copy_5(i * DIM, outer_public_memory + i * DIM)

    public_memory_random_point = Array(outer_public_memory_log_size * DIM)
    for i in range(0, outer_public_memory_log_size):
        copy_5(fs_sample_ef(fs), public_memory_random_point + i * DIM)
        fs = duplexing(fs)
    poly_eq_public_mem = poly_eq_extension_dynamic(public_memory_random_point, outer_public_memory_log_size)
    public_memory_eval = Array(DIM)
    dot_product_be_dynamic(
        outer_public_memory,
        poly_eq_public_mem,
        public_memory_eval,
        powers_of_two(outer_public_memory_log_size),
    )

    # WHIR BASE
    combination_randomness_gen: Mut = fs_sample_ef(fs)
    combination_randomness_powers: Mut = powers_const(
        combination_randomness_gen, WHIR_NUM_OOD_COMMIT + TOTAL_WHIR_STATEMENTS
    )
    whir_sum: Mut = dot_product_ret(whir_base_ood_evals, combination_randomness_powers, WHIR_NUM_OOD_COMMIT, EE)
    curr_randomness: Mut = combination_randomness_powers + WHIR_NUM_OOD_COMMIT * DIM

    whir_sum = add_extension_ret(mul_extension_ret(value_memory, curr_randomness), whir_sum)
    curr_randomness += DIM
    whir_sum = add_extension_ret(mul_extension_ret(value_acc, curr_randomness), whir_sum)
    curr_randomness += DIM
    whir_sum = add_extension_ret(mul_extension_ret(public_memory_eval, curr_randomness), whir_sum)
    curr_randomness += DIM

    whir_sum = add_extension_ret(mul_extension_ret(embed_in_ef(STARTING_PC), curr_randomness), whir_sum)
    curr_randomness += DIM
    whir_sum = add_extension_ret(mul_extension_ret(embed_in_ef(ENDING_PC), curr_randomness), whir_sum)
    curr_randomness += DIM

    for table_index in unroll(0, N_TABLES):
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
        whir_base_root,
        whir_base_ood_points,
        combination_randomness_powers,
        whir_sum,
    )

    curr_randomness = combination_randomness_powers + WHIR_NUM_OOD_COMMIT * DIM

    eq_memory_and_acc_point = eq_mle_extension(
        folding_randomness_global + (WHIR_N_VARS - log_memory) * DIM,
        memory_and_acc_point,
        log_memory,
    )
    prefix_mem = multilinear_location_prefix(0, WHIR_N_VARS - log_memory, folding_randomness_global)
    s = add_extension_ret(
        s,
        mul_extension_ret(mul_extension_ret(curr_randomness, prefix_mem), eq_memory_and_acc_point),
    )
    curr_randomness += DIM

    prefix_acc = multilinear_location_prefix(1, WHIR_N_VARS - log_memory, folding_randomness_global)
    s = add_extension_ret(
        s,
        mul_extension_ret(mul_extension_ret(curr_randomness, prefix_acc), eq_memory_and_acc_point),
    )
    curr_randomness += DIM

    eq_pub_mem = eq_mle_extension(
        folding_randomness_global + (WHIR_N_VARS - outer_public_memory_log_size) * DIM,
        public_memory_random_point,
        outer_public_memory_log_size,
    )
    prefix_pub_mem = multilinear_location_prefix(
        0, WHIR_N_VARS - outer_public_memory_log_size, folding_randomness_global
    )
    s = add_extension_ret(
        s,
        mul_extension_ret(mul_extension_ret(curr_randomness, prefix_pub_mem), eq_pub_mem),
    )
    curr_randomness += DIM

    offset = powers_of_two(log_memory) * 2  # memory and acc

    prefix_pc_start = multilinear_location_prefix(
        offset + COL_PC * powers_of_two(log_n_cycles),
        WHIR_N_VARS,
        folding_randomness_global,
    )
    s = add_extension_ret(s, mul_extension_ret(curr_randomness, prefix_pc_start))
    curr_randomness += DIM

    prefix_pc_end = multilinear_location_prefix(
        offset + (COL_PC + 1) * powers_of_two(log_n_cycles) - 1,
        WHIR_N_VARS,
        folding_randomness_global,
    )
    s = add_extension_ret(s, mul_extension_ret(curr_randomness, prefix_pc_end))
    curr_randomness += DIM

    for table_index in unroll(0, N_TABLES):
        log_n_rows = table_dims[table_index]
        n_rows = powers_of_two(log_n_rows)
        total_num_cols = NUM_COLS_F_AIR[table_index] + DIM * NUM_COLS_EF_AIR[table_index]
        for i in unroll(0, len(pcs_points[table_index])):
            point = pcs_points[table_index][i]
            eq_factor = eq_mle_extension(
                point,
                folding_randomness_global + (WHIR_N_VARS - log_n_rows) * DIM,
                log_n_rows,
            )
            for j in unroll(0, total_num_cols):
                if len(pcs_values[table_index][i][j]) == 1:
                    prefix = multilinear_location_prefix(
                        offset / n_rows + j,
                        WHIR_N_VARS - log_n_rows,
                        folding_randomness_global,
                    )
                    s = add_extension_ret(
                        s,
                        mul_extension_ret(mul_extension_ret(curr_randomness, prefix), eq_factor),
                    )
                    curr_randomness += DIM
        num_committed_cols: Imu
        if table_index == EXECUTION_TABLE_INDEX:
            num_committed_cols = N_COMMITTED_EXEC_COLUMNS
        else:
            num_committed_cols = total_num_cols
        offset += n_rows * num_committed_cols

    copy_5(mul_extension_ret(s, final_value), end_sum)

    # Last TODO = Opening on the guest bytecode, but there are multiple ways to handle this

    return


def multilinear_location_prefix(offset, n_vars, point):
    bits = checked_decompose_bits_small_value(offset, n_vars)
    res = eq_mle_base_extension(bits, point, n_vars)
    return res


def fingerprint_2(table_index, data_1, data_2, alpha_powers):
    buff = Array(DIM * 2)
    copy_5(data_1, buff)
    copy_5(data_2, buff + DIM)
    res: Mut = dot_product_ret(buff, alpha_powers + DIM, 2, EE)
    res = add_base_extension_ret(table_index, res)
    return res


def verify_gkr_quotient(fs: Mut, n_vars):
    fs, nums = fs_receive_ef(fs, 2)
    fs, denoms = fs_receive_ef(fs, 2)

    q1 = div_extension_ret(nums, denoms)
    q2 = div_extension_ret(nums + DIM, denoms + DIM)
    quotient = add_extension_ret(q1, q2)

    points = Array(n_vars)
    claims_num = Array(n_vars)
    claims_den = Array(n_vars)

    points[0] = fs_sample_ef(fs)
    fs = duplexing(fs)

    point_poly_eq = poly_eq_extension(points[0], 1)

    first_claim_num = dot_product_ret(nums, point_poly_eq, 2, EE)
    first_claim_den = dot_product_ret(denoms, point_poly_eq, 2, EE)
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
    alpha = fs_sample_ef(fs)
    alpha_mul_claim_den = mul_extension_ret(alpha, claim_den)
    num_plus_alpha_mul_claim_den = add_extension_ret(claim_num, alpha_mul_claim_den)
    postponed_point = Array((n_vars + 1) * DIM)
    fs, postponed_value = sumcheck_verify_helper(fs, n_vars, num_plus_alpha_mul_claim_den, 3, postponed_point + DIM)
    fs, inner_evals = fs_receive_ef(fs, 4)
    a_num = inner_evals
    b_num = inner_evals + DIM
    a_den = inner_evals + 2 * DIM
    b_den = inner_evals + 3 * DIM
    sum_num, sum_den = sum_2_ef_fractions(a_num, a_den, b_num, b_den)
    sum_den_mul_alpha = mul_extension_ret(sum_den, alpha)
    sum_num_plus_sum_den_mul_alpha = add_extension_ret(sum_num, sum_den_mul_alpha)
    eq_factor = eq_mle_extension(point, postponed_point + DIM, n_vars)
    mul_extension(sum_num_plus_sum_den_mul_alpha, eq_factor, postponed_value)

    beta = fs_sample_ef(fs)
    fs = duplexing(fs)
    point_poly_eq = poly_eq_extension(beta, 1)
    new_claim_num = dot_product_ret(inner_evals, point_poly_eq, 2, EE)
    new_claim_den = dot_product_ret(inner_evals + 2 * DIM, point_poly_eq, 2, EE)

    copy_5(beta, postponed_point)

    return fs, postponed_point, new_claim_num, new_claim_den


def evaluate_air_constraints(table_index, inner_evals, air_alpha_powers, bus_beta, bus_alpha_powers):
    res: Imu
    debug_assert(table_index < 3)
    match table_index:
        case 0:
            res = evaluate_air_constraints_table_0(inner_evals, air_alpha_powers, bus_beta, bus_alpha_powers)
        case 1:
            res = evaluate_air_constraints_table_1(inner_evals, air_alpha_powers, bus_beta, bus_alpha_powers)
        case 2:
            res = evaluate_air_constraints_table_2(inner_evals, air_alpha_powers, bus_beta, bus_alpha_powers)
    return res


EVALUATE_AIR_FUNCTIONS_PLACEHOLDER
