from snark_lib import *
from whir import *
from hashing import *
from jagged_bp import *

N_TABLES = N_TABLES_PLACEHOLDER
N_SUB_TABLES = N_SUB_TABLES_PLACEHOLDER
# Number of jagged-PCS claims the inner prover packs into `v_combined`.
# Used to size the `alpha` sample vector right before WHIR. Matches the
# claim list built by `crates/lean_prover/src/prove_execution.rs::build_jagged_claims`
# (5 fixed: memory, memory_acc, public_memory, bytecode_acc, pc_start;
# plus per-table AIR up/down column claims).
N_JAGGED_CLAIMS = N_JAGGED_CLAIMS_PLACEHOLDER

# Per-sub-table log_widths (length N_SUB_TABLES). Sub-tables 0..2 are the
# memory / memory_acc / bytecode_acc sub-tables (log_width = 0); the rest
# come from decompose_table_widths per AIR table in ALL_TABLES order.
SUB_TABLE_LOG_WIDTHS = SUB_TABLE_LOG_WIDTHS_PLACEHOLDER
# Map (AIR table index, AIR column index) -> jagged sub-table coordinates.
AIR_COL_SUB_TABLE_ID = AIR_COL_SUB_TABLE_ID_PLACEHOLDER
AIR_COL_IN_SUB_TABLE = AIR_COL_IN_SUB_TABLE_PLACEHOLDER
PC_LOC_SUB_TABLE_ID = PC_LOC_SUB_TABLE_ID_PLACEHOLDER
PC_LOC_COL_IN_SUB_TABLE = PC_LOC_COL_IN_SUB_TABLE_PLACEHOLDER
# Padding-value kinds per (table, AIR col): 0 = zero, 1 = fixed scalar,
# 2 = padding_zero_vec_ptr, 3 = null_hash_ptr (= padding_zero_vec_ptr + 16).
PADDING_KIND = PADDING_KIND_PLACEHOLDER
PADDING_FIXED_VALUE = PADDING_FIXED_VALUE_PLACEHOLDER
PC_PAD_KIND = PC_PAD_KIND_PLACEHOLDER
PC_PAD_FIXED = PC_PAD_FIXED_PLACEHOLDER

# Jagged-assist sub-protocol metadata. The Rust prover emits one
# `target_g` + `log_width_g`-round sumcheck per group; the zkDSL verifier
# below reads and verifies them, reducing K=169 BP evaluations of F(i*)
# to one BP eval per group.
N_ASSIST_GROUPS = N_ASSIST_GROUPS_PLACEHOLDER
ASSIST_GROUP_TYPE = ASSIST_GROUP_TYPE_PLACEHOLDER  # 0=mem,1=mem_acc,2=pub_mem,3=bc_acc,4=pc_start,5+t=AIR table t
ASSIST_GROUP_SUB_TABLE_ID = ASSIST_GROUP_SUB_TABLE_ID_PLACEHOLDER
ASSIST_GROUP_IS_NEXT = ASSIST_GROUP_IS_NEXT_PLACEHOLDER
ASSIST_GROUP_LOG_WIDTH = ASSIST_GROUP_LOG_WIDTH_PLACEHOLDER
ASSIST_GROUP_N_CLAIMS = ASSIST_GROUP_N_CLAIMS_PLACEHOLDER
ASSIST_GROUP_CLAIM_OFFSET = ASSIST_GROUP_CLAIM_OFFSET_PLACEHOLDER
ASSIST_GROUP_COL_LISTS = ASSIST_GROUP_COL_LISTS_PLACEHOLDER  # [[col_in_st, ...]; N_ASSIST_GROUPS]
GROUP_TYPE_MEMORY = GROUP_TYPE_MEMORY_PLACEHOLDER
GROUP_TYPE_MEMORY_ACC = GROUP_TYPE_MEMORY_ACC_PLACEHOLDER
GROUP_TYPE_PUBLIC_MEMORY = GROUP_TYPE_PUBLIC_MEMORY_PLACEHOLDER
GROUP_TYPE_BYTECODE_ACC = GROUP_TYPE_BYTECODE_ACC_PLACEHOLDER
GROUP_TYPE_PC_START = GROUP_TYPE_PC_START_PLACEHOLDER
GROUP_TYPE_AIR_BASE = GROUP_TYPE_AIR_BASE_PLACEHOLDER

# `(p + 1) / 2` for KoalaBear (p = 2^31 - 2^24 + 1). Used as the inverse
# of 2 in the degree-2 Lagrange interpolation in the assist sumcheck.
JAGGED_ASSIST_INV_2 = 1065353217

LOGUP_GKR_N_VARS_TO_SEND_COEFFS = LOGUP_GKR_N_VARS_TO_SEND_COEFFS_PLACEHOLDER
LOGUP_GKR_N_COEFFS_SENT = 2**LOGUP_GKR_N_VARS_TO_SEND_COEFFS

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
LOGUP_CLAIM_COLUMNS = LOGUP_CLAIM_COLUMNS_PLACEHOLDER  # [[_; ?]; N_TABLES] sorted by ColIndex

NUM_COLS_AIR = NUM_COLS_AIR_PLACEHOLDER

AIR_DEGREES = AIR_DEGREES_PLACEHOLDER  # [_; N_TABLES]
MAX_AIR_FULL_DEGREE = MAX_AIR_FULL_DEGREE_PLACEHOLDER
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
INNER_PUBLIC_MEMORY_LOG_SIZE = 3 # public input = 1 hash digest = 8 field elements
PUB_INPUT_SIZE = DIGEST_LEN  # the public input is a single digest


def recursion(inner_public_memory, bytecode_hash_domsep):
    proof_transcript_size_buf = Array(1)
    hint_witness("proof_transcript_size", proof_transcript_size_buf)
    proof_transcript = Array(proof_transcript_size_buf[0])
    hint_witness("proof_transcript", proof_transcript)
    fs: Mut = fs_new(proof_transcript)

    fs = fs_observe(fs, inner_public_memory, PUB_INPUT_SIZE)  # observe public input (the data digest)
    fs = fs_observe(fs, bytecode_hash_domsep, DIGEST_LEN)  # observe hash(bytecode hash, domain sep)

    # table dims
    # The jagged-branch Rust prover writes (in this order):
    #   [whir_log_inv_rate, log_memory, public_input_len, padding_zero_vec_ptr,
    #    log_n_rows_per_table[0..N_TABLES], non_padded_n_rows_per_table[0..N_TABLES]]
    # = 4 + 2*N_TABLES scalars, padded by the FS framework to the next
    # multiple of 8 (= 16 for N_TABLES = 3, i.e. 2 chunks).
    debug_assert(4 + 2 * N_TABLES <= 16)
    fs, dims = fs_receive_chunks(fs, 2)
    for i in unroll(4 + 2 * N_TABLES, 16):
        assert dims[i] == 0
    whir_log_inv_rate = dims[0]
    log_memory = dims[1]
    public_input_len = dims[2]
    padding_zero_vec_ptr = dims[3]
    table_log_heights = dims + 4
    table_non_padded_n_rows = dims + 4 + N_TABLES

    assert public_input_len == PUB_INPUT_SIZE

    assert MIN_WHIR_LOG_INV_RATE <= whir_log_inv_rate
    assert whir_log_inv_rate <= MAX_WHIR_LOG_INV_RATE

    log_n_cycles = table_log_heights[EXECUTION_TABLE_INDEX]
    assert log_n_cycles <= log_memory

    log_bytecode_padded = maximum(LOG_GUEST_BYTECODE_LEN, log_n_cycles)

    table_heights = Array(N_TABLES)
    for i in unroll(0, N_TABLES):
        table_log_height = table_log_heights[i]
        table_heights[i] = two_exp(table_log_height)
        assert table_log_height <= log_n_cycles
        assert MIN_LOG_N_ROWS_PER_TABLE <= table_log_height
        assert table_log_height <= MAX_LOG_N_ROWS_PER_TABLE[i]
    assert MIN_LOG_MEMORY_SIZE <= log_memory
    assert log_memory <= MAX_LOG_MEMORY_SIZE
    assert LOG_GUEST_BYTECODE_LEN <= log_memory

    stacked_n_vars = compute_stacked_n_vars(log_memory, LOG_GUEST_BYTECODE_LEN, table_non_padded_n_rows)
    assert stacked_n_vars <= TWO_ADICITY + WHIR_INITIAL_FOLDING_FACTOR - whir_log_inv_rate

    # JAGGED-PCS: read the cumulative-area bit strings the prover wrote
    # before the WHIR commitment. `jagged_commit` (Rust prover) calls
    # `add_base_scalars(&usize_to_bits(area, m))` once per cumulative area
    # (= N_SUB_TABLES + 1 calls), each padded by the FS framework to the
    # next multiple of 8. We absorb them and store one pointer per area
    # for later use by `bp_eval` (F(i*) at WHIR's final folding point).
    # Booleanity is checked inside `read_cumulative_areas`; monotonicity
    # is implied (and currently elided) -- TODO before unconditional use.
    cumulative_area_ptrs: Mut = Array(N_SUB_TABLES + 1)
    fs = read_cumulative_areas(fs, stacked_n_vars, cumulative_area_ptrs)

    num_oods = get_num_oods(whir_log_inv_rate, stacked_n_vars)
    num_ood_at_commitment = num_oods[0]
    fs, whir_base_root, whir_base_ood_points, whir_base_ood_evals = parse_commitment(fs, num_ood_at_commitment)

    fs, logup_c = fs_sample_ef(fs)

    fs, logup_alphas = fs_sample_many_ef(fs, log2_ceil(MAX_BUS_WIDTH))

    logup_alphas_eq_poly = compute_eq_mle_extension(logup_alphas, log2_ceil(MAX_BUS_WIDTH))

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
    retrieved_denominators_value: Mut = mul_extension_ret(memory_and_acc_prefix, sub_extension_ret(logup_c, fingerprint_memory))

    offset: Mut = two_exp(log_memory)

    bytecode_and_acc_point = point_gkr + (n_vars_logup_gkr - LOG_GUEST_BYTECODE_LEN) * DIM
    bytecode_multilinear_location_prefix = multilinear_location_prefix(
        offset / 2**LOG_GUEST_BYTECODE_LEN, n_vars_logup_gkr - LOG_GUEST_BYTECODE_LEN, point_gkr
    )
    bytecode_padded_multilinear_location_prefix = multilinear_location_prefix(
        offset / two_exp(log_bytecode_padded), n_vars_logup_gkr - log_bytecode_padded, point_gkr
    )
    # Build padded claim data: [point | value | zero padding]
    bytecode_claim = Array(BYTECODE_CLAIM_SIZE_PADDED)
    copy_many_ef(bytecode_and_acc_point, bytecode_claim, LOG_GUEST_BYTECODE_LEN)
    copy_many_ef(
        logup_alphas + (log2_ceil(MAX_BUS_WIDTH) - log2_ceil(N_INSTRUCTION_COLUMNS)) * DIM,
        bytecode_claim + LOG_GUEST_BYTECODE_LEN * DIM,
        log2_ceil(N_INSTRUCTION_COLUMNS),
    )
    hint_witness("bytecode_value_hint", bytecode_claim + BYTECODE_POINT_N_VARS * DIM)
    for k in unroll(BYTECODE_CLAIM_SIZE, BYTECODE_CLAIM_SIZE_PADDED):
        bytecode_claim[k] = 0
    bytecode_value = bytecode_claim + BYTECODE_POINT_N_VARS * DIM
    bytecode_value_corrected: Mut = bytecode_value
    for i in unroll(0, log2_ceil(MAX_BUS_WIDTH) - log2_ceil(N_INSTRUCTION_COLUMNS)):
        bytecode_value_corrected = mul_extension_ret(bytecode_value_corrected, one_minus_self_extension_ret(logup_alphas + i * DIM))

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
                        mul_base_extension_ret(LOGUP_BYTECODE_DOMAINSEP, logup_alphas_eq_poly + (2 ** log2_ceil(MAX_BUS_WIDTH) - 1) * DIM),
                    ),
                ),
            ),
        ),
    )
    retrieved_denominators_value = add_extension_ret(
        retrieved_denominators_value,
        mul_extension_ret(
            bytecode_padded_multilinear_location_prefix,
            mle_of_zeros_then_ones_pow2(
                point_gkr + (n_vars_logup_gkr - log_bytecode_padded) * DIM,
                LOG_GUEST_BYTECODE_LEN,
                log_bytecode_padded,
            ),
        ),
    )
    offset += two_exp(log_bytecode_padded)

    # Dispatch based on table height ordering (sorted by descending height)
    if maximum(table_log_heights[1], table_log_heights[2]) == table_log_heights[1]:
        continue_recursion_ordered(
            1,
            2,
            fs,
            offset,
            retrieved_numerators_value,
            retrieved_denominators_value,
            table_heights,
            table_log_heights,
            point_gkr,
            n_vars_logup_gkr,
            logup_alphas_eq_poly,
            logup_c,
            numerators_value,
            denominators_value,
            log_memory,
            inner_public_memory,
            stacked_n_vars,
            whir_log_inv_rate,
            whir_base_root,
            whir_base_ood_points,
            whir_base_ood_evals,
            num_ood_at_commitment,
            log_n_cycles,
            log_bytecode_padded,
            bytecode_and_acc_point,
            value_memory,
            value_acc,
            value_bytecode_acc,
            padding_zero_vec_ptr,
            cumulative_area_ptrs,
            table_non_padded_n_rows,
        )
    else:
        continue_recursion_ordered(
            2,
            1,
            fs,
            offset,
            retrieved_numerators_value,
            retrieved_denominators_value,
            table_heights,
            table_log_heights,
            point_gkr,
            n_vars_logup_gkr,
            logup_alphas_eq_poly,
            logup_c,
            numerators_value,
            denominators_value,
            log_memory,
            inner_public_memory,
            stacked_n_vars,
            whir_log_inv_rate,
            whir_base_root,
            whir_base_ood_points,
            whir_base_ood_evals,
            num_ood_at_commitment,
            log_n_cycles,
            log_bytecode_padded,
            bytecode_and_acc_point,
            value_memory,
            value_acc,
            value_bytecode_acc,
            padding_zero_vec_ptr,
            cumulative_area_ptrs,
            table_non_padded_n_rows,
        )

    return bytecode_claim


@inline
def continue_recursion_ordered(
    second_table,
    third_table,
    fs,
    offset,
    retrieved_numerators_value,
    retrieved_denominators_value,
    table_heights,
    table_log_heights,
    point_gkr,
    n_vars_logup_gkr,
    logup_alphas_eq_poly,
    logup_c,
    numerators_value,
    denominators_value,
    log_memory,
    inner_public_memory,
    stacked_n_vars,
    whir_log_inv_rate,
    whir_base_root,
    whir_base_ood_points,
    whir_base_ood_evals,
    num_ood_at_commitment,
    log_n_cycles,
    log_bytecode_padded,
    bytecode_and_acc_point,
    value_memory,
    value_acc,
    value_bytecode_acc,
    padding_zero_vec_ptr,
    cumulative_area_ptrs,
    table_non_padded_n_rows,
):
    bus_numerators_values = DynArray([])
    bus_denominators_values = DynArray([])
    pcs_points = DynArray([])  # [[_; N]; N_TABLES]
    for i in unroll(0, N_TABLES):
        pcs_points.push(DynArray([]))
    pcs_values = DynArray([])  # [[[[] or [_]; num cols]; N]; N_TABLES]
    pcs_values_down = DynArray([])  # same structure, for next_mle-weighted column evals
    for i in unroll(0, N_TABLES):
        pcs_values.push(DynArray([]))
        pcs_values_down.push(DynArray([]))
    # gkr-time column evaluations at the inner point. They're absorbed into the AIR
    # sumcheck initial sum (one alpha-power slot per logup-claim column) instead of
    # being separate WHIR statements.
    gkr_evals = DynArray([])  # [[[] or [_]; num cols]; N_TABLES]
    for i in unroll(0, N_TABLES):
        gkr_evals.push(DynArray([]))
        total_num_cols = NUM_COLS_AIR[i]
        for _ in unroll(0, total_num_cols):
            gkr_evals[i].push(DynArray([]))

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

        if table_index == EXECUTION_TABLE_INDEX:
            # 0] Bytecode lookup
            bytecode_prefix = multilinear_location_prefix(offset / n_rows, n_vars_logup_gkr - log_n_rows, point_gkr)

            fs, eval_on_pc = fs_receive_ef_inlined(fs, 1)
            gkr_evals[EXECUTION_TABLE_INDEX][COL_PC].push(eval_on_pc)
            fs, instr_evals = fs_receive_ef_inlined(fs, N_INSTRUCTION_COLUMNS)
            for i in unroll(0, N_INSTRUCTION_COLUMNS):
                global_index = N_COMMITTED_EXEC_COLUMNS + i
                gkr_evals[EXECUTION_TABLE_INDEX][global_index].push(instr_evals + i * DIM)
            retrieved_numerators_value = add_extension_ret(retrieved_numerators_value, bytecode_prefix)
            fingerp = fingerprint_bytecode(instr_evals, eval_on_pc, logup_alphas_eq_poly)
            retrieved_denominators_value = add_extension_ret(
                retrieved_denominators_value,
                mul_extension_ret(bytecode_prefix, sub_extension_ret(logup_c, fingerp)),
            )
            offset += n_rows

        prefix = multilinear_location_prefix(offset / n_rows, n_vars_logup_gkr - log_n_rows, point_gkr)

        fs, eval_on_selector = fs_receive_ef_inlined(fs, 1)
        retrieved_numerators_value = add_extension_ret(retrieved_numerators_value, mul_extension_ret(prefix, eval_on_selector))

        fs, eval_on_data = fs_receive_ef_inlined(fs, 1)
        retrieved_denominators_value = add_extension_ret(retrieved_denominators_value, mul_extension_ret(prefix, eval_on_data))

        bus_numerators_values.push(eval_on_selector)

        bus_denominators_values.push(eval_on_data)

        offset += n_rows

        # II] Lookup into memory

        for lookup_f_index in unroll(0, len(LOOKUPS_INDEXES[table_index])):
            col_index = LOOKUPS_INDEXES[table_index][lookup_f_index]
            fs, index_eval = fs_receive_ef_inlined(fs, 1)
            debug_assert(len(gkr_evals[table_index][col_index]) == 0)
            gkr_evals[table_index][col_index].push(index_eval)
            for i in unroll(0, len(LOOKUPS_VALUES[table_index][lookup_f_index])):
                fs, value_eval = fs_receive_ef_inlined(fs, 1)
                col_index = LOOKUPS_VALUES[table_index][lookup_f_index][i]
                debug_assert(len(gkr_evals[table_index][col_index]) == 0)
                gkr_evals[table_index][col_index].push(value_eval)

                pref = multilinear_location_prefix(offset / n_rows, n_vars_logup_gkr - log_n_rows, point_gkr)  # TODO there is some duplication here
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

    # VERIFY BUS AND AIR — back-loaded batched sumcheck (see https://hackmd.io/s/HyxaupAAA)

    fs, bus_beta = fs_sample_ef(fs)
    fs, air_alpha = fs_sample_ef(fs)
    air_alpha_powers = powers_const(air_alpha, MAX_NUM_AIR_CONSTRAINTS + 1)
    fs, eta = fs_sample_ef(fs)
    eta_powers = powers_const(eta, N_TABLES)

    initial_sum: Mut = ZERO_VEC_PTR
    for sorted_pos in unroll(0, N_TABLES):
        table_index: Imu
        if sorted_pos == 0:
            table_index = EXECUTION_TABLE_INDEX
        if sorted_pos == 1:
            table_index = second_table
        if sorted_pos == 2:
            table_index = third_table
        bus_numerator_value = bus_numerators_values[sorted_pos]
        bus_denominator_value = bus_denominators_values[sorted_pos]

        bus_final_value: Mut = bus_numerator_value
        if table_index != EXECUTION_TABLE_INDEX:
            bus_final_value = opposite_extension_ret(bus_final_value)
        bus_final_value = add_extension_ret(
            bus_final_value,
            mul_extension_ret(bus_beta, sub_extension_ret(bus_denominator_value, logup_c)),
        )

        # Each logup-claim column adds `alpha_powers[1+j] * v_col_j` to the per-table
        # AIR sumcheck initial sum (matching the prover's BUS=true Air::eval, which
        # emits one virtual column per logup-claim column right after the bus virtual
        # column).
        logup_extra_sum: Mut = ZERO_VEC_PTR
        if table_index == EXECUTION_TABLE_INDEX:
            for j in unroll(0, len(LOGUP_CLAIM_COLUMNS[EXECUTION_TABLE_INDEX])):
                col = LOGUP_CLAIM_COLUMNS[EXECUTION_TABLE_INDEX][j]
                logup_extra_sum = add_extension_ret(
                    logup_extra_sum,
                    mul_extension_ret(air_alpha_powers + (1 + j) * DIM, gkr_evals[EXECUTION_TABLE_INDEX][col][0]),
                )
        if table_index == second_table:
            for j in unroll(0, len(LOGUP_CLAIM_COLUMNS[second_table])):
                col = LOGUP_CLAIM_COLUMNS[second_table][j]
                logup_extra_sum = add_extension_ret(
                    logup_extra_sum,
                    mul_extension_ret(air_alpha_powers + (1 + j) * DIM, gkr_evals[second_table][col][0]),
                )
        if table_index == third_table:
            for j in unroll(0, len(LOGUP_CLAIM_COLUMNS[third_table])):
                col = LOGUP_CLAIM_COLUMNS[third_table][j]
                logup_extra_sum = add_extension_ret(
                    logup_extra_sum,
                    mul_extension_ret(air_alpha_powers + (1 + j) * DIM, gkr_evals[third_table][col][0]),
                )
        initial_table_sum = add_extension_ret(bus_final_value, logup_extra_sum)
        initial_sum = add_extension_ret(initial_sum, mul_extension_ret(eta_powers + sorted_pos * DIM, initial_table_sum))

    n_max = log_n_cycles # extension table is always the biggest
    # Batched AIR sumcheck:
    fs, all_challenges, batched_air_final_value = sumcheck_verify_reversed(fs, n_max, initial_sum, MAX_AIR_FULL_DEGREE)

    check_sum: Mut = ZERO_VEC_PTR
    for sorted_pos in unroll(0, N_TABLES):
        table_index: Imu
        if sorted_pos == 0:
            table_index = EXECUTION_TABLE_INDEX
        if sorted_pos == 1:
            table_index = second_table
        if sorted_pos == 2:
            table_index = third_table
        log_n_rows = table_log_heights[table_index]
        total_num_cols = NUM_COLS_AIR[table_index]
        n_up_columns = N_AIR_COLUMNS[table_index]
        n_down_columns = len(AIR_DOWN_COLUMNS[table_index])

        fs, inner_evals = fs_receive_ef_inlined(fs, n_up_columns + n_down_columns)

        air_constraints_eval = evaluate_air_constraints(table_index, inner_evals, air_alpha_powers, bus_beta, logup_alphas_eq_poly)

        # bus_point = the GKR suffix for this table (= old `inner_point`).
        bus_point = point_gkr + (n_vars_logup_gkr - log_n_rows) * DIM
        eq_val = poly_eq_extension_dynamic_ret(bus_point, all_challenges, log_n_rows)

        k_t = product_first_n(all_challenges + log_n_rows * DIM, n_max - log_n_rows)

        contribution = mul_extension_ret(
            mul_extension_ret(eta_powers + sorted_pos * DIM, k_t),
            mul_extension_ret(eq_val, air_constraints_eval),
        )
        check_sum = add_extension_ret(check_sum, contribution)

        pcs_points[table_index].push(all_challenges)
        pcs_values[table_index].push(DynArray([]))
        pcs_values_down[table_index].push(DynArray([]))
        last_index = len(pcs_values[table_index]) - 1
        for _ in unroll(0, total_num_cols):
            pcs_values[table_index][last_index].push(DynArray([]))
            pcs_values_down[table_index][last_index].push(DynArray([]))
        for i in unroll(0, n_up_columns):
            pcs_values[table_index][last_index][i].push(inner_evals + i * DIM)
        if len(AIR_DOWN_COLUMNS[table_index]) != 0:
            evals_down = inner_evals + n_up_columns * DIM
            for i in unroll(0, n_down_columns):
                pcs_values_down[table_index][last_index][AIR_DOWN_COLUMNS[table_index][i]].push(evals_down + i * DIM)

    # verify that the AIR-batched sumcheck is valid
    copy_5(check_sum, batched_air_final_value)

    fs, public_memory_random_point = fs_sample_many_ef(fs, INNER_PUBLIC_MEMORY_LOG_SIZE)
    poly_eq_public_mem = compute_eq_mle_extension(public_memory_random_point, INNER_PUBLIC_MEMORY_LOG_SIZE)
    public_memory_eval = Array(DIM)
    dot_product_be(inner_public_memory, poly_eq_public_mem, public_memory_eval, 2**INNER_PUBLIC_MEMORY_LOG_SIZE)

    # JAGGED-PCS: sample one batching alpha per claim. Mirrors the prover's
    # `jagged_open`, which calls `prover_state.sample()` once per claim
    # (i.e. `sample_vec(1)` repeatedly, not a batched `sample_vec(n)`).
    # We MUST replicate that exact per-call pattern so the FS state
    # advances identically. Alphas are not consumed yet -- `v_combined`
    # and `F(i*)` wiring is the next surgery step.
    jagged_alphas = Array(N_JAGGED_CLAIMS * DIM)
    alpha_tmp: Imu
    for i in unroll(0, N_JAGGED_CLAIMS):
        fs, alpha_tmp = fs_sample_ef(fs)
        copy_5(alpha_tmp, jagged_alphas + i * DIM)

    # JAGGED-PCS: build `v_combined = sum_j alpha_j * (value_j - pad_adj_j)`.
    # Mirrors `jagged_verify` in `crates/sub_protocols/src/jagged_pcs/verifier.rs`.
    # All 5 fixed claims have pad_adj = 0 (memory/memory_acc/public_memory/
    # bytecode_acc have padding_value=0, and pc_start has z_row=zeros with
    # n_zeros>0 so mle_of_zeros_then_ones=0). For per-table AIR claims:
    #   - UP cols have n_zeros = 2^log_height = n_values so mle = 0,
    #   - DOWN cols have n_zeros = 2^log_height - 1 < n_values so mle may be
    #     non-zero. Only DOWN cols with non-zero padding_value contribute.
    null_hash_ptr = padding_zero_vec_ptr + 16

    v_combined: Mut = Array(DIM)
    for k in unroll(0, DIM):
        v_combined[k] = 0

    claim_idx_runtime: Mut = 0
    alpha_ptr: Mut = jagged_alphas

    # Claim 0: memory
    alpha_ptr = jagged_alphas + claim_idx_runtime * DIM
    v_combined = add_extension_ret(v_combined, mul_extension_ret(alpha_ptr, value_memory))
    claim_idx_runtime += 1
    # Claim 1: memory_acc
    alpha_ptr = jagged_alphas + claim_idx_runtime * DIM
    v_combined = add_extension_ret(v_combined, mul_extension_ret(alpha_ptr, value_acc))
    claim_idx_runtime += 1
    # Claim 2: public_memory
    alpha_ptr = jagged_alphas + claim_idx_runtime * DIM
    v_combined = add_extension_ret(v_combined, mul_extension_ret(alpha_ptr, public_memory_eval))
    claim_idx_runtime += 1
    # Claim 3: bytecode_acc
    alpha_ptr = jagged_alphas + claim_idx_runtime * DIM
    v_combined = add_extension_ret(v_combined, mul_extension_ret(alpha_ptr, value_bytecode_acc))
    claim_idx_runtime += 1
    # Claim 4: pc_start (value = STARTING_PC, pad_adj = 0 since z_row=zeros)
    alpha_ptr = jagged_alphas + claim_idx_runtime * DIM
    v_combined = add_extension_ret(v_combined, mul_extension_ret(alpha_ptr, embed_in_ef(STARTING_PC)))
    claim_idx_runtime += 1

    # Per-AIR-table per-column claims. Iterate by ALL_TABLES order (0, 1, 2),
    # then UP cols (sorted by col_index), then DOWN cols (sorted by col_index).
    for table_index in unroll(0, N_TABLES):
        log_n_rows_t = table_log_heights[table_index]
        # Sub-table height is the NON-PADDED row count (matches the Rust
        # `SubTable { height: non_padded_per_table[t] }`), NOT 2^log_n_rows.
        # For is_next claims: n_zeros = h - 1 (else n_zeros = h).
        h_t = table_non_padded_n_rows[table_index]
        air_point = pcs_points[table_index][0]
        # Precompute the two indicator MLEs once per table (shared across all
        # cols of this table since they share the z_row = AIR sumcheck point).
        mle_up_t = mle_of_zeros_then_ones(air_point, h_t, log_n_rows_t)
        mle_dn_t = mle_of_zeros_then_ones(air_point, h_t - 1, log_n_rows_t)
        # UP cols: pad_adj = padding_value * mle_up_t
        for j in unroll(0, NUM_COLS_AIR[table_index]):
            up_value_ptr = pcs_values[table_index][0][j][0]
            alpha_ptr = jagged_alphas + claim_idx_runtime * DIM
            pad_kind = PADDING_KIND[table_index][j]
            if pad_kind == 0:
                v_combined = add_extension_ret(v_combined, mul_extension_ret(alpha_ptr, up_value_ptr))
            if pad_kind != 0:
                pad_val_base: Imu
                if pad_kind == 1:
                    pad_val_base = PADDING_FIXED_VALUE[table_index][j]
                if pad_kind == 2:
                    pad_val_base = padding_zero_vec_ptr
                if pad_kind == 3:
                    pad_val_base = null_hash_ptr
                if pad_kind == 4:
                    pad_val_base = padding_zero_vec_ptr + 4  # zero_vec_ptr + HALF_DIGEST_LEN
                pad_adj = mul_base_extension_ret(pad_val_base, mle_up_t)
                adjusted_value = sub_extension_ret(up_value_ptr, pad_adj)
                v_combined = add_extension_ret(v_combined, mul_extension_ret(alpha_ptr, adjusted_value))
            claim_idx_runtime += 1
        # DOWN cols: pad_adj = padding_value * mle_dn_t (only present for is_next claims)
        for j in unroll(0, NUM_COLS_AIR[table_index]):
            if len(pcs_values_down[table_index][0][j]) == 1:
                down_value_ptr = pcs_values_down[table_index][0][j][0]
                alpha_ptr = jagged_alphas + claim_idx_runtime * DIM
                pad_kind_dn = PADDING_KIND[table_index][j]
                if pad_kind_dn == 0:
                    v_combined = add_extension_ret(v_combined, mul_extension_ret(alpha_ptr, down_value_ptr))
                if pad_kind_dn != 0:
                    pad_val_base_dn: Imu
                    if pad_kind_dn == 1:
                        pad_val_base_dn = PADDING_FIXED_VALUE[table_index][j]
                    if pad_kind_dn == 2:
                        pad_val_base_dn = padding_zero_vec_ptr
                    if pad_kind_dn == 3:
                        pad_val_base_dn = null_hash_ptr
                    if pad_kind_dn == 4:
                        pad_val_base_dn = padding_zero_vec_ptr + 4
                    pad_adj_dn = mul_base_extension_ret(pad_val_base_dn, mle_dn_t)
                    adjusted_value_dn = sub_extension_ret(down_value_ptr, pad_adj_dn)
                    v_combined = add_extension_ret(v_combined, mul_extension_ret(alpha_ptr, adjusted_value_dn))
                claim_idx_runtime += 1
    assert claim_idx_runtime == N_JAGGED_CLAIMS

    # WHIR BASE
    combination_randomness_gen: Mut
    fs, combination_randomness_gen = fs_sample_ef(fs)
    combination_randomness_powers: Mut = powers(combination_randomness_gen, num_ood_at_commitment + 1)
    whir_sum: Mut = Array(DIM)
    dot_product_ee_dynamic(whir_base_ood_evals, combination_randomness_powers, whir_sum, num_ood_at_commitment)
    gamma_for_extra = combination_randomness_powers + num_ood_at_commitment * DIM
    whir_sum = add_extension_ret(whir_sum, mul_extension_ret(v_combined, gamma_for_extra))

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

    # JAGGED-PCS assist sub-protocol: replaces the per-claim BP eval loop
    # (K=N_JAGGED_CLAIMS BP evals) with a per-group sumcheck delegation.
    # See `crates/sub_protocols/src/jagged_pcs/assist.rs` for the Rust
    # prover side. Per group g, the prover sends `target_g` plus
    # `log_width_g`-round sumcheck transcripts; the verifier samples
    # challenges, computes `eq_combined_g = sum_j alpha_j * eq(rho_g, z_col_j)`,
    # does ONE `bp_eval` at `(z_row_g, rho_g, i_star, t_prev_g, t_next_g)`
    # and checks the sumcheck identity. F(i*) = sum_g target_g.

    # Pre-lift cumulative_area bits to EF representation.
    MAX_M = TWO_ADICITY + WHIR_INITIAL_FOLDING_FACTOR - MIN_WHIR_LOG_INV_RATE
    all_t_ef = Array((N_SUB_TABLES + 1) * MAX_M * DIM)
    for st_id in unroll(0, N_SUB_TABLES + 1):
        bits_ptr = cumulative_area_ptrs[st_id]
        out_base = all_t_ef + st_id * MAX_M * DIM
        for k in range(0, stacked_n_vars):
            out_base[k * DIM] = bits_ptr[k]
            for kk in unroll(1, DIM):
                out_base[k * DIM + kk] = 0

    # Pre-lift the shifted t_prev (= original + 2^log_width) for each AIR
    # sub-table that may host an is_next claim.
    shifted_t_ef = Array(N_SUB_TABLES * MAX_M * DIM)
    for st_id in unroll(3, N_SUB_TABLES):
        log_width_st = SUB_TABLE_LOG_WIDTHS[st_id]
        bits_ptr = cumulative_area_ptrs[st_id]
        out_base = shifted_t_ef + st_id * MAX_M * DIM
        shift_bits_and_lift(bits_ptr, stacked_n_vars, log_width_st, out_base)

    # Pre-build the z_rows for the fixed groups (memory, public_memory,
    # pc_start) which have non-trivial structure.
    # `pm_z_row`: pad_high(public_memory_random_point, log_memory).
    pm_z_row = Array(MAX_LOG_MEMORY_SIZE * DIM)
    n_pad_high = log_memory - INNER_PUBLIC_MEMORY_LOG_SIZE
    for k in range(0, n_pad_high):
        for kk in unroll(0, DIM):
            pm_z_row[k * DIM + kk] = 0
    for k in unroll(0, INNER_PUBLIC_MEMORY_LOG_SIZE):
        for kk in unroll(0, DIM):
            pm_z_row[(n_pad_high + k) * DIM + kk] = public_memory_random_point[k * DIM + kk]
    # `pc_z_row`: zeros of length log_n_cycles.
    pc_z_row = Array(MAX_LOG_N_ROWS_PER_TABLE[EXECUTION_TABLE_INDEX] * DIM)
    for k in range(0, log_n_cycles):
        for kk in unroll(0, DIM):
            pc_z_row[k * DIM + kk] = 0

    f_at_istar: Mut = Array(DIM)
    for k in unroll(0, DIM):
        f_at_istar[k] = 0

    for g in unroll(0, N_ASSIST_GROUPS):
        st_id = ASSIST_GROUP_SUB_TABLE_ID[g]
        log_width = ASSIST_GROUP_LOG_WIDTH[g]
        is_next = ASSIST_GROUP_IS_NEXT[g]
        n_claims = ASSIST_GROUP_N_CLAIMS[g]
        claim_offset = ASSIST_GROUP_CLAIM_OFFSET[g]
        group_type = ASSIST_GROUP_TYPE[g]

        # Dispatch to the right z_row pointer + length based on group_type.
        # `group_type` is a compile-time constant per iteration, so only one
        # branch is emitted into the bytecode.
        z_row_ptr: Imu
        z_row_len: Imu
        if group_type == GROUP_TYPE_MEMORY:
            z_row_ptr = memory_and_acc_point
            z_row_len = log_memory
        if group_type == GROUP_TYPE_MEMORY_ACC:
            z_row_ptr = memory_and_acc_point
            z_row_len = log_memory
        if group_type == GROUP_TYPE_PUBLIC_MEMORY:
            z_row_ptr = pm_z_row
            z_row_len = log_memory
        if group_type == GROUP_TYPE_BYTECODE_ACC:
            z_row_ptr = bytecode_and_acc_point
            z_row_len = LOG_GUEST_BYTECODE_LEN
        if group_type == GROUP_TYPE_PC_START:
            z_row_ptr = pc_z_row
            z_row_len = log_n_cycles
        if group_type == GROUP_TYPE_AIR_BASE + 0:
            z_row_ptr = pcs_points[0][0]
            z_row_len = table_log_heights[0]
        if group_type == GROUP_TYPE_AIR_BASE + 1:
            z_row_ptr = pcs_points[1][0]
            z_row_len = table_log_heights[1]
        if group_type == GROUP_TYPE_AIR_BASE + 2:
            z_row_ptr = pcs_points[2][0]
            z_row_len = table_log_heights[2]

        # t_prev: shifted if is_next.
        t_prev_ptr: Imu
        if is_next == 0:
            t_prev_ptr = all_t_ef + st_id * MAX_M * DIM
        if is_next == 1:
            t_prev_ptr = shifted_t_ef + st_id * MAX_M * DIM
        t_next_ptr = all_t_ef + (st_id + 1) * MAX_M * DIM

        # Read target_g from the FS transcript.
        fs, target_g = fs_receive_ef_inlined(fs, 1)

        if log_width == 0:
            # No sumcheck rounds: single claim, target_g == alpha_offset * h_g(()).
            debug_assert(n_claims == 1)
            h_at_rho = bp_eval(
                z_row_ptr, z_row_len, ZERO_VEC_PTR, 0, folding_randomness_global,
                t_prev_ptr, t_next_ptr, 0, stacked_n_vars,
            )
            alpha_ptr_only = jagged_alphas + claim_offset * DIM
            product = mul_extension_ret(h_at_rho, alpha_ptr_only)
            for k in unroll(0, DIM):
                assert target_g[k] == product[k]
        if log_width != 0:
            # Run log_width-round sumcheck.
            rho = Array(log_width * DIM)
            current_claim_sum: Mut = Array(DIM)
            copy_5(target_g, current_claim_sum)
            for j in unroll(0, log_width):
                fs, poly3 = fs_receive_ef_inlined(fs, 3)
                # P(0) + P(1) == current_claim_sum.
                for k in unroll(0, DIM):
                    assert poly3[k] + poly3[k + DIM] == current_claim_sum[k]
                # Sample challenge rho_j.
                fs, rho_j = fs_sample_ef(fs)
                copy_5(rho_j, rho + j * DIM)
                # current_claim_sum := P(rho_j) via Lagrange interp.
                current_claim_sum = interp_deg2_at(poly3, rho_j)

            # Compute eq_combined = sum_c alpha_{offset+c} * eq(rho, x_c).
            eq_combined: Mut = Array(DIM)
            for k in unroll(0, DIM):
                eq_combined[k] = 0
            for c in unroll(0, n_claims):
                col_in_st = ASSIST_GROUP_COL_LISTS[g][c]
                eq_val = compute_eq_for_const_col(rho, log_width, col_in_st)
                alpha_ptr_c = jagged_alphas + (claim_offset + c) * DIM
                eq_combined = add_extension_ret(eq_combined, mul_extension_ret(alpha_ptr_c, eq_val))

            # ONE BP eval per group, replacing K_g per-claim BP evals.
            h_at_rho = bp_eval(
                z_row_ptr, z_row_len, rho, log_width, folding_randomness_global,
                t_prev_ptr, t_next_ptr, log_width, stacked_n_vars,
            )
            product = mul_extension_ret(h_at_rho, eq_combined)
            for k in unroll(0, DIM):
                assert current_claim_sum[k] == product[k]

        f_at_istar = add_extension_ret(f_at_istar, target_g)

    s = add_extension_ret(s, mul_extension_ret(gamma_for_extra, f_at_istar))

    copy_5(mul_extension_ret(s, final_value), end_sum)
    return


def multilinear_location_prefix(offset, n_vars, point):
    bits = checked_decompose_bits_small_value(offset, n_vars)
    res = poly_eq_base_extension(bits, point, n_vars)
    return res


def fingerprint_2(table_index, data_1, data_2, logup_alphas_eq_poly):
    buff = Array(DIM * 2)
    copy_5(data_1, buff)
    copy_5(data_2, buff + DIM)
    res: Mut = dot_product_ee_ret(buff, logup_alphas_eq_poly, 2)
    res = add_extension_ret(res, mul_base_extension_ret(table_index, logup_alphas_eq_poly + (2 ** log2_ceil(MAX_BUS_WIDTH) - 1) * DIM))
    return res


@inline
def fingerprint_bytecode(instr_evals, eval_on_pc, logup_alphas_eq_poly):
    res: Mut = dot_product_ee_ret(instr_evals, logup_alphas_eq_poly, N_INSTRUCTION_COLUMNS)
    res = add_extension_ret(res, mul_extension_ret(eval_on_pc, logup_alphas_eq_poly + N_INSTRUCTION_COLUMNS * DIM))
    res = add_extension_ret(
        res,
        mul_base_extension_ret(LOGUP_BYTECODE_DOMAINSEP, logup_alphas_eq_poly + (2 ** log2_ceil(MAX_BUS_WIDTH) - 1) * DIM),
    )
    return res


def verify_gkr_quotient(fs: Mut, n_vars):
    fs, nums = fs_receive_ef_inlined(fs, LOGUP_GKR_N_COEFFS_SENT)
    fs, denoms = fs_receive_ef_inlined(fs, LOGUP_GKR_N_COEFFS_SENT)

    initial_quotients = Array(LOGUP_GKR_N_COEFFS_SENT * DIM)
    for k in unroll(0, LOGUP_GKR_N_COEFFS_SENT):
        div_extension(nums + k * DIM, denoms + k * DIM, initial_quotients + k * DIM)
    debug_assert(NUM_REPEATED_ONES <= LOGUP_GKR_N_COEFFS_SENT)
    debug_assert(LOGUP_GKR_N_COEFFS_SENT % NUM_REPEATED_ONES == 0)
    quotient: Mut = ZERO_VEC_PTR
    for k in unroll(0, LOGUP_GKR_N_COEFFS_SENT / NUM_REPEATED_ONES):
        quotient = add_extension_ret(quotient, sum_continuous_ef(initial_quotients + k * NUM_REPEATED_ONES * DIM, NUM_REPEATED_ONES))

    points = Array(n_vars)
    claims_num = Array(n_vars)
    claims_den = Array(n_vars)

    fs, initial_point = fs_sample_many_ef(fs, LOGUP_GKR_N_VARS_TO_SEND_COEFFS)
    points[LOGUP_GKR_N_VARS_TO_SEND_COEFFS - 1] = initial_point

    point_poly_eq = compute_eq_mle_extension(initial_point, LOGUP_GKR_N_VARS_TO_SEND_COEFFS)

    first_claim_num = dot_product_ee_ret(nums, point_poly_eq, LOGUP_GKR_N_COEFFS_SENT)
    first_claim_den = dot_product_ee_ret(denoms, point_poly_eq, LOGUP_GKR_N_COEFFS_SENT)
    claims_num[LOGUP_GKR_N_VARS_TO_SEND_COEFFS - 1] = first_claim_num
    claims_den[LOGUP_GKR_N_VARS_TO_SEND_COEFFS - 1] = first_claim_den

    for i in range(LOGUP_GKR_N_VARS_TO_SEND_COEFFS, n_vars):
        fs, points[i], claims_num[i], claims_den[i] = verify_gkr_quotient_step(fs, i, points[i - 1], claims_num[i - 1], claims_den[i - 1])

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
    fs, postponed_value = sumcheck_verify_reversed_helper(fs, n_vars, num_plus_alpha_mul_claim_den, 3, postponed_point)
    fs, inner_evals = fs_receive_ef_inlined(fs, 4)
    a_num = inner_evals
    b_num = inner_evals + DIM
    a_den = inner_evals + 2 * DIM
    b_den = inner_evals + 3 * DIM
    sum_num, sum_den = sum_2_ef_fractions(a_num, a_den, b_num, b_den)
    sum_den_mul_alpha = mul_extension_ret(sum_den, alpha)
    sum_num_plus_sum_den_mul_alpha = add_extension_ret(sum_num, sum_den_mul_alpha)
    eq_factor = poly_eq_extension_dynamic_ret(point, postponed_point, n_vars)
    mul_extension(sum_num_plus_sum_den_mul_alpha, eq_factor, postponed_value)

    fs, beta = fs_sample_ef(fs)

    point_poly_eq = compute_eq_mle_extension(beta, 1)
    new_claim_num = dot_product_ee_ret(inner_evals, point_poly_eq, 2)
    new_claim_den = dot_product_ee_ret(inner_evals + 2 * DIM, point_poly_eq, 2)

    copy_5(beta, postponed_point + n_vars * DIM)

    return fs, postponed_point, new_claim_num, new_claim_den


@inline
def compute_stacked_n_vars(log_memory, log_bytecode, tables_non_padded_n_rows):
    """Compute the jagged-PCS dense polynomial's `log_dense_size`. Mirrors
    Rust `JaggedConfig::new` ∘ `ZkvmJaggedLayout::new`: the AIR sub-tables
    use the actual NON-PADDED row counts (not `2^log_n_rows`), and
    bytecode_acc's height is `2^log_bytecode` (no `max(...)` -- that was
    the pre-jagged stacked-PCS layout).

    `total = 2 * 2^log_memory + 2^log_bytecode + sum_t n_cols_t * non_padded_n_rows[t]`,
    `log_dense_size = log2_ceil(total)`.

    With the bounds set by `MAX_LOG_MEMORY_SIZE = 26`,
    `MAX_LOG_N_ROWS_PER_TABLE = [24, 21, 21]`, the total is at most
    `2^28 + 2^19 + 20·2^24 + 29·2^21 + 100·2^21 < 2^30`, so
    `log2_ceil_runtime` works directly without scaling.
    """
    total: Mut = two_exp(log_memory + 1)  # memory + memory_acc (padded)
    total += two_exp(log_bytecode)  # bytecode_acc (padded)
    for table_index in unroll(0, N_TABLES):
        h = tables_non_padded_n_rows[table_index]
        total += h * NUM_COLS_AIR[table_index]
    return log2_ceil_runtime(total)


def compute_total_gkr_n_vars(log_memory, log_bytecode_padded, tables_heights):
    total: Mut = two_exp(log_memory)
    total += two_exp(log_bytecode_padded)
    total += tables_heights[EXECUTION_TABLE_INDEX]
    for table_index in unroll(0, N_TABLES):
        n_rows = tables_heights[table_index]
        total_lookup_values: Mut = 0
        for i in unroll(0, len(LOOKUPS_INDEXES[table_index])):
            total_lookup_values += len(LOOKUPS_VALUES[table_index][i])
        total_lookup_values += 1  # for the bus
        total += n_rows * total_lookup_values
    return log2_ceil_runtime(total)


def read_cumulative_areas(fs, m, area_ptrs: Mut):
    """Absorb N_SUB_TABLES + 1 jagged-PCS cumulative-area bit strings from
    the FS transcript and validate booleanity. Each string has `m` raw
    bits (= log_dense_size), framework-padded by the prover to the next
    multiple of 8. Writes one transcript pointer per area into
    `area_ptrs[0..N_SUB_TABLES + 1]` for later use by `bp_eval`.
    Dispatch on the runtime `m` at the top level (cheaper than
    dispatching per-area since `m` is shared across all areas)."""
    new_fs = match_range(
        m,
        range(MIN_STACKED_N_VARS, TWO_ADICITY + WHIR_INITIAL_FOLDING_FACTOR - MIN_WHIR_LOG_INV_RATE + 1),
        lambda mm: absorb_cumulative_areas_const(fs, mm, area_ptrs),
    )
    return new_fs


def shift_bits_and_lift(bits_in, m, log_width: Const, out_ef: Mut):
    """Compute `(bits_in + 2^log_width)` as base-field bits, then lift each
    bit to EF representation (bit at coord 0, zeros elsewhere) and write
    into `out_ef[k * DIM + kk]` for k in [0, m), kk in [0, DIM).
    `log_width` is compile-time, `m` is runtime."""
    # Copy unchanged tail [m - log_width, m) directly.
    n_tail = log_width  # number of bits below the addition point
    for k in range(m - n_tail, m):
        out_ef[k * DIM] = bits_in[k]
        for kk in unroll(1, DIM):
            out_ef[k * DIM + kk] = 0
    # Position m - 1 - log_width: this is where we add 1 (b=1, c_in=0).
    pos_first = m - 1 - n_tail
    a_first = bits_in[pos_first]
    out_ef[pos_first * DIM] = 1 - a_first
    for kk in unroll(1, DIM):
        out_ef[pos_first * DIM + kk] = 0
    # Carry propagates upward (lower index). Iterate k from pos_first-1
    # down to 0; carry_in for the next iteration is the carry_out of this.
    carry: Mut = a_first
    for k_rev in range(0, pos_first):
        k = pos_first - 1 - k_rev
        a = bits_in[k]
        out_bit = a + carry - 2 * a * carry
        out_ef[k * DIM] = out_bit
        for kk in unroll(1, DIM):
            out_ef[k * DIM + kk] = 0
        carry = a * carry
    assert carry == 0
    return


def interp_deg2_at(poly3, x):
    """Lagrange-interpolate the unique degree-2 polynomial through
    `(0, P(0)), (1, P(1)), (2, P(2))` and evaluate at `x`. `poly3` is a
    flat `3 * DIM` EF array storing `[P(0); P(1); P(2)]`. Returns a new
    `DIM`-element EF."""
    x_minus_1 = sub_extension_ret(x, ONE_EF_PTR)
    x_minus_2 = sub_extension_ret(x_minus_1, ONE_EF_PTR)
    # L_0 = (x-1)(x-2)/2; L_1 = -x(x-2); L_2 = x(x-1)/2
    x_m1_times_x_m2 = mul_extension_ret(x_minus_1, x_minus_2)
    l0_p0 = mul_extension_ret(x_m1_times_x_m2, poly3)
    l0_p0_half = mul_base_extension_ret(JAGGED_ASSIST_INV_2, l0_p0)

    x_times_x_m2 = mul_extension_ret(x, x_minus_2)
    minus_x_times_x_m2 = opposite_extension_ret(x_times_x_m2)
    l1_p1 = mul_extension_ret(minus_x_times_x_m2, poly3 + DIM)

    x_times_x_m1 = mul_extension_ret(x, x_minus_1)
    l2_p2 = mul_extension_ret(x_times_x_m1, poly3 + 2 * DIM)
    l2_p2_half = mul_base_extension_ret(JAGGED_ASSIST_INV_2, l2_p2)

    return add_extension_ret(add_extension_ret(l0_p0_half, l1_p1), l2_p2_half)


def compute_eq_for_const_col(rho, log_width: Const, col_in_st: Const):
    """Compute `eq(rho, bits(col_in_st))` where `bits(col_in_st)` is the
    big-endian boolean point of `col_in_st` in `log_width` bits.

    `eq` factors:
        bit k of `col_in_st` (MSB-first) == 0  ->  factor = (1 - rho[k])
        bit k of `col_in_st` (MSB-first) == 1  ->  factor =      rho[k]

    Returns an EF pointer of length DIM. For `log_width == 0` returns
    `ONE_EF_PTR` (the identity element)."""
    if log_width == 0:
        return ONE_EF_PTR
    result: Mut = Array(DIM)
    copy_5(ONE_EF_PTR, result)
    for k in unroll(0, log_width):
        low_mod = 2 ** (log_width - k)
        high_pow = 2 ** (log_width - 1 - k)
        bit = div_floor(col_in_st % low_mod, high_pow)
        rho_k = rho + k * DIM
        factor: Imu
        if bit == 0:
            factor = one_minus_self_extension_ret(rho_k)
        if bit == 1:
            factor = rho_k
        result = mul_extension_ret(result, factor)
    return result


def absorb_cumulative_areas_const(fs: Mut, m: Const, area_ptrs: Mut):
    # `m` is the bit-count per cumulative area, fixed at compile time
    # by the outer `match_range` dispatch.
    n_chunks = div_ceil(m, 8)
    n_remainder = 8 * n_chunks - m
    for i in unroll(0, N_SUB_TABLES + 1):
        fs, area_data = fs_receive_chunks(fs, n_chunks)
        # Booleanity: each of the m real bits must be in {0, 1}.
        for k in unroll(0, m):
            bit = area_data[k]
            assert bit * (1 - bit) == 0
        # The prover writes `m` real bits then `n_remainder` zero-padding
        # scalars; assert the padding so we don't accept malformed input.
        for k in unroll(m, m + n_remainder):
            assert area_data[k] == 0
        area_ptrs[i] = area_data
    return fs


def evaluate_air_constraints(table_index, inner_evals, air_alpha_powers, bus_beta, logup_alphas_eq_poly):
    res: Imu
    debug_assert(table_index < N_TABLES)
    match table_index:
        case 0:
            res = evaluate_air_constraints_table_0(inner_evals, air_alpha_powers, bus_beta, logup_alphas_eq_poly)
        case 1:
            res = evaluate_air_constraints_table_1(inner_evals, air_alpha_powers, bus_beta, logup_alphas_eq_poly)
        case 2:
            res = evaluate_air_constraints_table_2(inner_evals, air_alpha_powers, bus_beta, logup_alphas_eq_poly)
    return res


EVALUATE_AIR_FUNCTIONS_PLACEHOLDER
