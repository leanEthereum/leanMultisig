from snark_lib import *
from whir import *

N_TABLES = N_TABLES_PLACEHOLDER

MIN_LOG_N_ROWS_PER_TABLE = MIN_LOG_N_ROWS_PER_TABLE_PLACEHOLDER
MAX_LOG_N_ROWS_PER_TABLE = MAX_LOG_N_ROWS_PER_TABLE_PLACEHOLDER
MIN_LOG_MEMORY_SIZE = MIN_LOG_MEMORY_SIZE_PLACEHOLDER
MAX_LOG_MEMORY_SIZE = MAX_LOG_MEMORY_SIZE_PLACEHOLDER
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
    pub_mem = NONRESERVED_PROGRAM_INPUT_START
    priv_start = pub_mem[0]
    proof_size = priv_start[0]
    inner_public_memory_log_size = priv_start[1]
    inner_public_memory_size = powers_of_two(inner_public_memory_log_size)
    n_recursions = priv_start[2]
    inner_public_memory = priv_start + 3
    proofs_start = inner_public_memory + inner_public_memory_size
    for i in range(0, n_recursions):
        proof_transcript = proofs_start + i * proof_size
        recursion(inner_public_memory_log_size, inner_public_memory, proof_transcript)
    return


def recursion(inner_public_memory_log_size, inner_public_memory, proof_transcript):
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

    log_bytecode = log2_ceil(GUEST_BYTECODE_LEN)
    log_bytecode_padded = maximum(log_bytecode, log_n_cycles)

    table_heights = Array(N_TABLES)
    for i in unroll(0, N_TABLES):
        table_log_height = table_log_heights[i]
        table_heights[i] = powers_of_two(table_log_height)
        assert table_log_height <= log_n_cycles
        assert MIN_LOG_N_ROWS_PER_TABLE <= table_log_height
        assert table_log_height <= MAX_LOG_N_ROWS_PER_TABLE[i]
    assert MIN_LOG_MEMORY_SIZE <= log_memory
    assert log_memory <= MAX_LOG_MEMORY_SIZE
    assert log_memory <= GUEST_BYTECODE_LEN

    stacked_n_vars = compute_stacked_n_vars(log_memory, log_bytecode_padded, table_heights)
    assert stacked_n_vars <= TWO_ADICITY + WHIR_INITIAL_FOLDING_FACTOR - whir_log_inv_rate

    num_oods = get_num_oods(stacked_n_vars, whir_log_inv_rate)
    num_ood_at_commitment = num_oods[0]
    fs, whir_base_root, whir_base_ood_points, whir_base_ood_evals = parse_commitment(fs, num_ood_at_commitment)

    fs, logup_c = fs_sample_ef(fs)

    fs, logup_alphas = fs_sample_many_ef(fs, log2_ceil(MAX_BUS_WIDTH))

    logup_alphas_eq_poly = poly_eq_extension(logup_alphas, log2_ceil(MAX_BUS_WIDTH))

    # GENRIC LOGUP

    n_vars_logup_gkr = compute_total_gkr_n_vars(log_memory, log_bytecode_padded, table_heights)

    fs, quotient_gkr, point_gkr, numerators_value, denominators_value = verify_gkr_quotient(fs, n_vars_logup_gkr)
    set_to_5_zeros(quotient_gkr)

    memory_and_acc_prefix = multilinear_location_prefix(0, n_vars_logup_gkr - log_memory, point_gkr)

    fs, value_acc = fs_receive_ef_inlined(fs, 1)
    fs, value_memory = fs_receive_ef_inlined(fs, 1)

    retrieved_numerators_value: Mut = opposite_extension_ret(mul_extension_ret(memory_and_acc_prefix, value_acc))

    value_index = mle_of_01234567_etc(point_gkr + (n_vars_logup_gkr - log_memory) * DIM, log_memory)
    fingerprint_memory = fingerprint_2(MEMORY_TABLE_INDEX, value_memory, value_index, logup_alphas_eq_poly)
    retrieved_denominators_value: Mut = mul_extension_ret(
        memory_and_acc_prefix, sub_extension_ret(logup_c, fingerprint_memory)
    )

    offset: Mut = powers_of_two(log_memory)

    bytecode_and_acc_point = point_gkr + (n_vars_logup_gkr - log_bytecode) * DIM
    bytecode_multilinear_location_prefix = multilinear_location_prefix(
        offset / 2 ** log2_ceil(GUEST_BYTECODE_LEN), n_vars_logup_gkr - log_bytecode, point_gkr
    )
    bytecode_padded_multilinear_location_prefix = multilinear_location_prefix(
        offset / powers_of_two(log_bytecode_padded), n_vars_logup_gkr - log_bytecode_padded, point_gkr
    )
    pub_mem = NONRESERVED_PROGRAM_INPUT_START
    assert pub_mem[1] == log_bytecode + log2_ceil(N_INSTRUCTION_COLUMNS)
    copy_many_ef(bytecode_and_acc_point, pub_mem + 2, log_bytecode)
    copy_many_ef(
        logup_alphas + (log2_ceil(MAX_BUS_WIDTH) - log2_ceil(N_INSTRUCTION_COLUMNS)) * DIM,
        pub_mem + 2 + log_bytecode * DIM,
        log2_ceil(N_INSTRUCTION_COLUMNS),
    )
    bytecode_value = pub_mem + 2 + (log_bytecode + log2_ceil(N_INSTRUCTION_COLUMNS)) * DIM
    bytecode_value_corrected: Mut = bytecode_value
    for i in unroll(0, log2_ceil(MAX_BUS_WIDTH) - log2_ceil(N_INSTRUCTION_COLUMNS)):
        bytecode_value_corrected = mul_extension_ret(
            bytecode_value_corrected, one_minus_self_extension_ret(logup_alphas + i * DIM)
        )

    fs, value_bytecode_acc = fs_receive_ef_inlined(fs, 1)
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
                            BYTECODE_TABLE_INDEX, logup_alphas_eq_poly + (2 ** log2_ceil(MAX_BUS_WIDTH) - 1) * DIM
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
                2 ** log2_ceil(GUEST_BYTECODE_LEN),
                log_bytecode_padded,
            ),
        ),
    )
    offset += powers_of_two(log_bytecode_padded)

    bus_numerators_values = DynArray([])
    bus_denominators_values = DynArray([])
    pcs_points = DynArray([])  # [[_; N]; N_TABLES]
    for i in unroll(0, N_TABLES):
        pcs_points.push(DynArray([]))
    pcs_values = DynArray([])  # [[[[] or [_]; num cols]; N]; N_TABLES]
    for i in unroll(0, N_TABLES):
        pcs_values.push(DynArray([]))
        pcs_values[i].push(DynArray([]))
        total_num_cols = NUM_COLS_F_AIR[i] + DIM * NUM_COLS_EF_AIR[i]
        for _ in unroll(0, total_num_cols):
            pcs_values[i][0].push(DynArray([]))

    for table_index in unroll(0, N_TABLES):
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

        for lookup_f_index in unroll(0, len(LOOKUPS_F_INDEXES[table_index])):
            col_index = LOOKUPS_F_INDEXES[table_index][lookup_f_index]
            fs, index_eval = fs_receive_ef_inlined(fs, 1)
            debug_assert(len(pcs_values[table_index][0][col_index]) == 0)
            pcs_values[table_index][0][col_index].push(index_eval)
            for i in unroll(0, len(LOOKUPS_F_VALUES[table_index][lookup_f_index])):
                fs, value_eval = fs_receive_ef_inlined(fs, 1)
                col_index = LOOKUPS_F_VALUES[table_index][lookup_f_index][i]
                debug_assert(len(pcs_values[table_index][0][col_index]) == 0)
                pcs_values[table_index][0][col_index].push(value_eval)

                pref = multilinear_location_prefix(
                    offset / n_rows, n_vars_logup_gkr - log_n_rows, point_gkr
                )  # TODO there is some duplication here
                retrieved_numerators_value = add_extension_ret(retrieved_numerators_value, pref)
                fingerp = fingerprint_2(
                    MEMORY_TABLE_INDEX,
                    value_eval,
                    add_base_extension_ret(i, index_eval),
                    logup_alphas_eq_poly,
                )
                retrieved_denominators_value = add_extension_ret(
                    retrieved_denominators_value,
                    mul_extension_ret(pref, sub_extension_ret(logup_c, fingerp)),
                )

                offset += n_rows

        for lookup_ef_index in unroll(0, len(LOOKUPS_EF_INDEXES[table_index])):
            col_index = LOOKUPS_EF_INDEXES[table_index][lookup_ef_index]
            fs, index_eval = fs_receive_ef_inlined(fs, 1)
            if len(pcs_values[table_index][0][col_index]) == 0:
                pcs_values[table_index][0][col_index].push(index_eval)
            else:
                # assert equal
                copy_5(index_eval, pcs_values[table_index][0][col_index][0])

            for i in unroll(0, DIM):
                fs, value_eval = fs_receive_ef_inlined(fs, 1)
                pref = multilinear_location_prefix(
                    offset / n_rows, n_vars_logup_gkr - log_n_rows, point_gkr
                )  # TODO there is some duplication here
                retrieved_numerators_value = add_extension_ret(retrieved_numerators_value, pref)
                fingerp = fingerprint_2(
                    MEMORY_TABLE_INDEX,
                    value_eval,
                    add_base_extension_ret(i, index_eval),
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

    for table_index in unroll(0, N_TABLES):
        log_n_rows = table_log_heights[table_index]
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
        fs, inner_evals = fs_receive_ef_inlined(fs, n_up_columns + n_down_columns)

        air_constraints_eval = evaluate_air_constraints(
            table_index, inner_evals, air_alpha_powers, bus_beta, logup_alphas_eq_poly
        )
        expected_outer_eval = mul_extension_ret(
            air_constraints_eval,
            eq_mle_extension(zerocheck_challenges, outer_point, log_n_rows),
        )
        copy_5(expected_outer_eval, outer_eval)

        if len(AIR_DOWN_COLUMNS_F[table_index]) != 0:
            fs, batching_scalar = fs_sample_ef(fs)
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

            fs, evals_f_on_down_columns = fs_receive_ef_inlined(fs, n_down_columns_f)
            batched_col_down_sc_eval: Mut = dot_product_ret(
                evals_f_on_down_columns, batching_scalar_powers, n_down_columns_f, EE
            )

            evals_ef_on_down_columns: Imu
            if n_down_columns_ef != 0:
                fs, evals_ef_on_down_columns = fs_receive_ef_inlined(fs, n_down_columns_ef)
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
                fs, transposed = fs_receive_ef_inlined(fs, DIM)
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
            fs, transposed = fs_receive_ef_inlined(fs, DIM)
            copy_5(
                inner_evals + (n_up_columns_f + n_down_columns_f + i) * DIM,
                dot_product_with_the_base_vectors(transposed),
            )
            for j in unroll(0, DIM):
                virtual_col_index = n_up_columns_f + i * DIM + j
                pcs_values[table_index][last_index_2][virtual_col_index].push(transposed + j * DIM)

    # verify the inner public memory is well constructed (with the conventions) (NONRESERVED_PROGRAM_INPUT_START is a multiple of DIM)
    for i in unroll(0, NONRESERVED_PROGRAM_INPUT_START / DIM):
        copy_5(i * DIM, inner_public_memory + i * DIM)

    fs, public_memory_random_point = fs_sample_many_ef(fs, inner_public_memory_log_size)
    poly_eq_public_mem = poly_eq_extension_dynamic(public_memory_random_point, inner_public_memory_log_size)
    public_memory_eval = Array(DIM)
    dot_product_be_dynamic(
        inner_public_memory,
        poly_eq_public_mem,
        public_memory_eval,
        powers_of_two(inner_public_memory_log_size),
    )

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
        folding_randomness_global + (stacked_n_vars - inner_public_memory_log_size) * DIM,
        public_memory_random_point,
        inner_public_memory_log_size,
    )
    prefix_pub_mem = multilinear_location_prefix(
        0, stacked_n_vars - inner_public_memory_log_size, folding_randomness_global
    )
    s = add_extension_ret(
        s,
        mul_extension_ret(mul_extension_ret(curr_randomness, prefix_pub_mem), eq_pub_mem),
    )
    curr_randomness += DIM

    offset = powers_of_two(log_memory) * 2  # memory and acc_memory

    eq_bytecode_acc = eq_mle_extension(
        folding_randomness_global + (stacked_n_vars - log2_ceil(GUEST_BYTECODE_LEN)) * DIM,
        bytecode_and_acc_point,
        log2_ceil(GUEST_BYTECODE_LEN),
    )
    prefix_bytecode_acc = multilinear_location_prefix(
        offset / 2 ** log2_ceil(GUEST_BYTECODE_LEN),
        stacked_n_vars - log2_ceil(GUEST_BYTECODE_LEN),
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

    for table_index in unroll(0, N_TABLES):
        log_n_rows = table_log_heights[table_index]
        n_rows = table_heights[table_index]
        total_num_cols = NUM_COLS_F_AIR[table_index] + DIM * NUM_COLS_EF_AIR[table_index]
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
    res: Mut = dot_product_ret(buff, logup_alphas_eq_poly, 2, EE)
    res = add_extension_ret(
        res, mul_base_extension_ret(table_index, logup_alphas_eq_poly + (2 ** log2_ceil(MAX_BUS_WIDTH) - 1) * DIM)
    )
    return res


def fingerprint_bytecode(instr_evals, eval_on_pc, logup_alphas_eq_poly):
    res: Mut = dot_product_ret(instr_evals, logup_alphas_eq_poly, N_INSTRUCTION_COLUMNS, EE)
    res = add_extension_ret(res, mul_extension_ret(eval_on_pc, logup_alphas_eq_poly + N_INSTRUCTION_COLUMNS * DIM))
    res = add_extension_ret(
        res,
        mul_base_extension_ret(BYTECODE_TABLE_INDEX, logup_alphas_eq_poly + (2 ** log2_ceil(MAX_BUS_WIDTH) - 1) * DIM),
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
    new_claim_num = dot_product_ret(inner_evals, point_poly_eq, 2, EE)
    new_claim_den = dot_product_ret(inner_evals + 2 * DIM, point_poly_eq, 2, EE)

    copy_5(beta, postponed_point)

    return fs, postponed_point, new_claim_num, new_claim_den


@inline
def compute_stacked_n_vars(log_memory, log_bytecode_padded, tables_heights):
    total: Mut = powers_of_two(log_memory + 1) # memory + acc_memory
    total += powers_of_two(log_bytecode_padded)
    for table_index in unroll(0, N_TABLES):
        n_rows = tables_heights[table_index]
        total += n_rows * (NUM_COLS_F_AIR[table_index] + DIM * NUM_COLS_EF_AIR[table_index])
    debug_assert(30 - 24 < MIN_LOG_N_ROWS_PER_TABLE) # cf log2_ceil
    return MIN_LOG_N_ROWS_PER_TABLE + log2_ceil_runtime(total / 2**MIN_LOG_N_ROWS_PER_TABLE)

def compute_total_gkr_n_vars(log_memory, log_bytecode_padded, tables_heights):
    total: Mut = powers_of_two(log_memory)
    total += powers_of_two(log_bytecode_padded)
    total += tables_heights[EXECUTION_TABLE_INDEX]
    for table_index in unroll(0, N_TABLES):
        n_rows = tables_heights[table_index]
        total_lookup_values: Mut = 0
        for i in unroll(0, len(LOOKUPS_F_INDEXES[table_index])):
            total_lookup_values += len(LOOKUPS_F_VALUES[table_index][i])
        total_lookup_values += DIM * len(LOOKUPS_EF_VALUES[table_index])
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
