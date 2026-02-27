use backend::*;
use lean_vm::*;
use poseidon_gkr::fill_poseidon_trace;
use tracing::info_span;
use std::{array, collections::BTreeMap};
use utils::{ToUsize, transposed_par_iter_mut};

#[derive(Debug)]
pub struct ExecutionTrace {
    pub traces: BTreeMap<Table, TableTrace>,
    pub public_memory_size: usize,
    pub non_zero_memory_size: usize,
    pub memory: Vec<F>, // of length a multiple of public_memory_size
    pub metadata: ExecutionMetadata,
}

pub fn get_execution_trace(bytecode: &Bytecode, execution_result: ExecutionResult) -> ExecutionTrace {
    assert_eq!(execution_result.pcs.len(), execution_result.fps.len());

    let n_cycles = execution_result.pcs.len();
    let memory = &execution_result.memory;
    let mut main_trace: [Vec<F>; N_TOTAL_EXECUTION_COLUMNS + N_TEMPORARY_EXEC_COLUMNS] =
        array::from_fn(|_| F::zero_vec(n_cycles.next_power_of_two()));
    for col in &mut main_trace {
        unsafe {
            col.set_len(n_cycles);
        }
    }

    transposed_par_iter_mut(&mut main_trace)
        .zip(execution_result.pcs.par_iter())
        .zip(execution_result.fps.par_iter())
        .for_each(|((trace_row, &pc), &fp)| {
            let instruction = &bytecode.instructions[pc];
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
            let value_a = memory.0.get(addr_a.to_usize()).copied().flatten().unwrap_or_default();

            let mut addr_b = F::ZERO;
            if flag_b.is_zero() && flag_ab_fp.is_zero() {
                addr_b = F::from_usize(fp) + field_repr[instr_idx(COL_OPERAND_B)];
            } else if is_deref {
                // DEREF: addr_B = value_A + operand_B
                addr_b = value_a + field_repr[instr_idx(COL_OPERAND_B)];
            }
            let value_b = memory.0.get(addr_b.to_usize()).copied().flatten().unwrap_or_default();

            let mut addr_c = F::ZERO;
            if flag_c.is_zero() && flag_c_fp.is_zero() {
                addr_c = F::from_usize(fp) + field_repr[instr_idx(COL_OPERAND_C)];
            }
            let value_c = memory.0.get(addr_c.to_usize()).copied().flatten().unwrap_or_default();

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
            if let Instruction::Precompile { .. } = instruction {
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

    let mut memory_padded = memory.0.par_iter().map(|&v| v.unwrap_or(F::ZERO)).collect::<Vec<F>>();
    // IMPRTANT: memory size should always be >= number of VM cycles
    let padded_memory_len = (memory.0.len().max(n_cycles).max(1 << MIN_LOG_N_ROWS_PER_TABLE)).next_power_of_two();
    memory_padded.resize(padded_memory_len, F::ZERO);

    let ExecutionResult { mut traces, .. } = execution_result;

    let extension_op_trace = traces.get_mut(&Table::extension_op()).unwrap();
    fill_trace_extension_op(extension_op_trace, &memory_padded);

    traces.insert(
        Table::execution(),
        TableTrace {
            base: Vec::from(main_trace),
            non_padded_n_rows: n_cycles,
            log_n_rows: log2_ceil_usize(n_cycles),
        },
    );
    for table in traces.keys().copied().collect::<Vec<_>>() {
        padd_table(&table, &mut traces);
    }

    // Fill GKR layers and compressed outputs in poseidon trace
    info_span!("Poseidon GKR trace fill").in_scope(|| {
        fill_poseidon_trace(&mut traces.get_mut(&Table::poseidon16()).unwrap().base);
    });

    ExecutionTrace {
        traces,
        public_memory_size: execution_result.public_memory_size,
        non_zero_memory_size: memory.0.len(),
        memory: memory_padded,
        metadata: execution_result.metadata,
    }
}

fn padd_table(table: &Table, traces: &mut BTreeMap<Table, TableTrace>) {
    let trace = traces.get_mut(table).unwrap();
    let h = trace.base[0].len();

    trace.non_padded_n_rows = h;
    trace.log_n_rows = log2_ceil_usize(h + 1).max(MIN_LOG_N_ROWS_PER_TABLE);
    let n_rows = 1 << trace.log_n_rows;
    let padding_row = table.padding_row();
    trace.base.par_iter_mut().enumerate().for_each(|(i, col)| {
        assert!(col.len() <= h); // potentially some columns have not been filled (in Poseidon16 -> we fill it later with SIMD + parallelism), but the first one should always be representative
        col.resize(n_rows, padding_row[i]);
    });
}
