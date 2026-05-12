use backend::*;
use lean_vm::*;
use std::collections::BTreeMap;
use utils::{ToUsize, get_poseidon_16_of_zero, transposed_par_iter_mut};

#[derive(Debug)]
pub struct ExecutionTrace {
    pub traces: BTreeMap<Table, TableTrace>,
    pub public_memory_size: usize,
    /// Memory padded to a power of two. Stored as `SlotColumn` so it can be either an owned
    /// `Vec<F>` (default) or a slot into the prover's pre-allocated stacked WHIR polynomial.
    pub memory: SlotColumn,
    pub metadata: ExecutionMetadata,
}

pub fn get_execution_trace(bytecode: &Bytecode, execution_result: ExecutionResult) -> ExecutionTrace {
    get_execution_trace_with_overrides(bytecode, execution_result, &BTreeMap::new())
}

/// Like `get_execution_trace`, but lets the caller pin each table's `log_n_rows` to a (possibly
/// over-estimating) value — used by the hinted prover path so that the column padding and the
/// prover-committed log sizes match the layout that was pre-allocated from the hint.
pub fn get_execution_trace_with_overrides(
    bytecode: &Bytecode,
    execution_result: ExecutionResult,
    log_n_rows_overrides: &BTreeMap<Table, usize>,
) -> ExecutionTrace {
    assert_eq!(execution_result.pcs.len(), execution_result.fps.len());

    let ExecutionResult {
        memory,
        pcs,
        fps,
        mut traces,
        public_memory_size,
        metadata,
        ..
    } = execution_result;

    let n_cycles = pcs.len();

    // Reuse the existing execution-table TableTrace slot. Slot-backed columns (allocated by the
    // direct-write prover path) already point into the stacked WHIR polynomial; owned columns
    // (default runner / tests path) grow on `resize`. Either way, we resize each column to
    // `n_cycles` here before the parallel fill below writes into them.
    let exec_trace = traces.entry(Table::execution()).or_default();
    assert_eq!(
        exec_trace.columns.len(),
        N_TOTAL_EXECUTION_COLUMNS + N_TEMPORARY_EXEC_COLUMNS,
        "execution TableTrace must have all (committed + virtual) columns pre-allocated"
    );
    for col in &mut exec_trace.columns {
        col.resize(n_cycles, F::ZERO);
    }
    let main_trace: &mut [SlotColumn; N_TOTAL_EXECUTION_COLUMNS + N_TEMPORARY_EXEC_COLUMNS] = (&mut exec_trace.columns
        [..])
        .try_into()
        .expect("execution columns length mismatch");

    transposed_par_iter_mut(main_trace)
        .zip(&pcs)
        .zip(&fps)
        .for_each(|((trace_row, &pc), &fp)| {
            let instruction = &bytecode.code[pc].instruction;
            let field_repr = &bytecode.instructions_multilinear[pc * N_INSTRUCTION_COLUMNS.next_power_of_two()..]
                [..N_INSTRUCTION_COLUMNS];

            let flag_a = field_repr[instr_idx(COL_FLAG_A)];
            let flag_b = field_repr[instr_idx(COL_FLAG_B)];
            let flag_c = field_repr[instr_idx(COL_FLAG_C)];
            let flag_c_fp = field_repr[instr_idx(COL_FLAG_C_FP)];
            let flag_ab_fp = field_repr[instr_idx(COL_FLAG_AB_FP)];
            let aux = field_repr[instr_idx(COL_AUX)];
            let is_deref = aux == F::TWO;

            let mut addr_a = F::ZERO;
            if flag_a.is_zero() && flag_ab_fp.is_zero() {
                addr_a = F::from_usize(fp) + field_repr[instr_idx(COL_OPERAND_A)];
            }
            let value_a = memory.get(addr_a.to_usize()).unwrap_or(F::ZERO);

            let mut addr_b = F::ZERO;
            if flag_b.is_zero() && flag_ab_fp.is_zero() {
                addr_b = F::from_usize(fp) + field_repr[instr_idx(COL_OPERAND_B)];
            } else if is_deref {
                // DEREF: addr_B = value_A + operand_B
                addr_b = value_a + field_repr[instr_idx(COL_OPERAND_B)];
            }
            let value_b = memory.get(addr_b.to_usize()).unwrap_or(F::ZERO);

            let mut addr_c = F::ZERO;
            if flag_c.is_zero() && flag_c_fp.is_zero() {
                addr_c = F::from_usize(fp) + field_repr[instr_idx(COL_OPERAND_C)];
            }
            let value_c = memory.get(addr_c.to_usize()).unwrap_or(F::ZERO);

            for (j, field) in field_repr.iter().enumerate() {
                *trace_row[j + N_RUNTIME_COLUMNS] = *field;
            }

            let nu_a = flag_a * field_repr[instr_idx(COL_OPERAND_A)]
                + (F::ONE - flag_a - flag_ab_fp) * value_a
                + flag_ab_fp * (F::from_usize(fp) + field_repr[instr_idx(COL_OPERAND_A)]);
            let nu_b = flag_b * field_repr[instr_idx(COL_OPERAND_B)]
                + (F::ONE - flag_b - flag_ab_fp) * value_b
                + flag_ab_fp * (F::from_usize(fp) + field_repr[instr_idx(COL_OPERAND_B)]);
            let nu_c = flag_c * field_repr[instr_idx(COL_OPERAND_C)]
                + (F::ONE - flag_c - flag_c_fp) * value_c
                + flag_c_fp * (F::from_usize(fp) + field_repr[instr_idx(COL_OPERAND_C)]);
            if let Instruction::Precompile(..) = instruction {
                *trace_row[COL_IS_PRECOMPILE] = F::ONE;
            }
            *trace_row[COL_EXEC_NU_A] = nu_a;
            *trace_row[COL_EXEC_NU_B] = nu_b;
            *trace_row[COL_EXEC_NU_C] = nu_c;

            *trace_row[COL_MEM_VALUE_A] = value_a;
            *trace_row[COL_MEM_VALUE_B] = value_b;
            *trace_row[COL_MEM_VALUE_C] = value_c;
            *trace_row[COL_PC] = F::from_usize(pc);
            *trace_row[COL_FP] = F::from_usize(fp);
            *trace_row[COL_MEM_ADDRESS_A] = addr_a;
            *trace_row[COL_MEM_ADDRESS_B] = addr_b;
            *trace_row[COL_MEM_ADDRESS_C] = addr_c;
        });

    let mut memory_padded: SlotColumn = memory.values;

    // Write [0000000000000000 | poseidon_compress(0000000000000000)] (to make lookups work on padding-rows).
    let padding_zero_vec_ptr = memory_padded.len();
    memory_padded.extend(std::iter::repeat_n(F::ZERO, 16));
    let null_poseidon_16_hash_ptr = memory_padded.len();
    memory_padded.extend_from_slice(get_poseidon_16_of_zero());

    // IMPORTANT: memory size should always be >= number of VM cycles
    let padded_memory_len = (memory_padded.len().max(n_cycles).max(1 << MIN_LOG_N_ROWS_PER_TABLE)).next_power_of_two();
    memory_padded.resize(padded_memory_len, F::ZERO);

    let poseidon_trace = traces.get_mut(&Table::poseidon16()).unwrap();
    fill_trace_poseidon_16(&mut poseidon_trace.columns);

    // For half_output rows, override last 4 output columns with actual memory values
    // (the AIR doesn't constrain them, but the lookup checks against memory).
    {
        let split = POSEIDON_16_COL_OUTPUT_START + HALF_DIGEST_LEN;
        let (left, right) = poseidon_trace.columns.split_at_mut(split);
        let half_output_col = &left[POSEIDON_16_COL_FLAG_HALF_OUTPUT];
        let res_col = &left[POSEIDON_16_COL_INDEX_INPUT_RES];
        let output_cols: &mut [SlotColumn; HALF_DIGEST_LEN] = (&mut right[..HALF_DIGEST_LEN]).try_into().unwrap();

        transposed_par_iter_mut(output_cols)
            .zip(half_output_col.as_slice())
            .zip(res_col.as_slice())
            .for_each(|((row, &half), &res)| {
                if half == F::ONE {
                    let base = res.to_usize() + HALF_DIGEST_LEN;
                    for j in 0..HALF_DIGEST_LEN {
                        *row[j] = memory_padded[base + j];
                    }
                }
            });
    }

    let extension_op_trace = traces.get_mut(&Table::extension_op()).unwrap();
    fill_trace_extension_op(extension_op_trace, &memory_padded);

    {
        let exec_trace = traces.get_mut(&Table::execution()).unwrap();
        exec_trace.non_padded_n_rows = n_cycles;
        exec_trace.log_n_rows = log2_ceil_usize(n_cycles);
    }
    for table in traces.keys().copied().collect::<Vec<_>>() {
        pad_table(
            &table,
            &mut traces,
            padding_zero_vec_ptr,
            null_poseidon_16_hash_ptr,
            log_n_rows_overrides.get(&table).copied(),
        );
    }

    ExecutionTrace {
        traces,
        public_memory_size,
        memory: memory_padded,
        metadata,
    }
}

fn pad_table(
    table: &Table,
    traces: &mut BTreeMap<Table, TableTrace>,
    zero_vec_ptr: usize,
    null_poseidon_16_hash_ptr: usize,
    log_n_rows_override: Option<usize>,
) {
    let trace = traces.get_mut(table).unwrap();
    let h = trace.columns[0].len();
    trace
        .columns
        .iter()
        .enumerate()
        .for_each(|(i, col)| assert_eq!(col.len(), h, "column {}, table {}", i, table.name()));

    trace.non_padded_n_rows = h;
    let natural_log = log2_ceil_usize(h + 1).max(MIN_LOG_N_ROWS_PER_TABLE);
    trace.log_n_rows = match log_n_rows_override {
        Some(o) => {
            assert!(
                o >= natural_log,
                "log_n_rows override {} too small for table {} (needs >= {})",
                o,
                table.name(),
                natural_log,
            );
            o
        }
        None => natural_log,
    };
    let n_rows = 1 << trace.log_n_rows;
    let padding_row = table.padding_row(zero_vec_ptr, null_poseidon_16_hash_ptr);
    trace.columns.par_iter_mut().enumerate().for_each(|(i, col)| {
        assert!(col.len() <= h); // potentially some columns have not been filled (in Poseidon -> we fill it later with SIMD + parallelism), but the first one should always be representative
        col.resize(n_rows, padding_row[i]);
    });
}
