use crate::instruction_encoder::field_representation;
use lean_vm::*;
use multilinear_toolkit::prelude::*;
use std::{array, collections::BTreeMap, iter::repeat_n};
use utils::{ToUsize, transposed_par_iter_mut};

#[derive(Debug)]
pub struct ExecutionTrace {
    pub traces: BTreeMap<Table, TableTrace>,
    pub public_memory_size: usize,
    pub non_zero_memory_size: usize,
    pub memory: Vec<F>, // of length a multiple of public_memory_size
}

pub fn get_execution_trace(bytecode: &Bytecode, execution_result: ExecutionResult) -> ExecutionTrace {
    assert_eq!(execution_result.pcs.len(), execution_result.fps.len());

    let n_cycles = execution_result.pcs.len();
    let memory = &execution_result.memory;
    let mut main_trace: [Vec<F>; N_EXEC_AIR_COLUMNS + N_TEMPORARY_EXEC_COLUMNS] =
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
            let field_repr = field_representation(instruction);

            let mut addr_a = F::ZERO;
            if field_repr[instr_idx(COL_FLAG_A)].is_zero() {
                // flag_a == 0
                addr_a = F::from_usize(fp) + field_repr[instr_idx(COL_OPERAND_A)]; // fp + operand_a
            }
            let value_a = memory.0[addr_a.to_usize()].unwrap();
            let mut addr_b = F::ZERO;
            if field_repr[instr_idx(COL_FLAG_B)].is_zero() {
                // flag_b == 0
                addr_b = F::from_usize(fp) + field_repr[instr_idx(COL_OPERAND_B)]; // fp + operand_b
            }
            let value_b = memory.0[addr_b.to_usize()].unwrap();

            let mut addr_c = F::ZERO;
            if field_repr[instr_idx(COL_FLAG_C)].is_zero() {
                // flag_c == 0
                addr_c = F::from_usize(fp) + field_repr[instr_idx(COL_OPERAND_C)]; // fp + operand_c
            } else if let Instruction::Deref { shift_1, .. } = instruction {
                let operand_c = F::from_usize(*shift_1);
                assert_eq!(field_repr[instr_idx(COL_OPERAND_C)], operand_c); // debug purpose
                addr_c = value_a + operand_c;
            }
            let value_c = memory.0[addr_c.to_usize()].unwrap();

            for (j, field) in field_repr.iter().enumerate() {
                *trace_row[j + N_COMMITTED_EXEC_COLUMNS] = *field;
            }

            let nu_a = field_repr[instr_idx(COL_FLAG_A)] * field_repr[instr_idx(COL_OPERAND_A)]
                + (F::ONE - field_repr[instr_idx(COL_FLAG_A)]) * value_a;
            let nu_b = field_repr[instr_idx(COL_FLAG_B)] * field_repr[instr_idx(COL_OPERAND_B)]
                + (F::ONE - field_repr[instr_idx(COL_FLAG_B)]) * value_b;
            let nu_c = field_repr[instr_idx(COL_FLAG_C)] * F::from_usize(fp)
                + (F::ONE - field_repr[instr_idx(COL_FLAG_C)]) * value_c;
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

    let poseidon_trace = traces.get_mut(&Table::poseidon16()).unwrap();
    fill_trace_poseidon_16(&mut poseidon_trace.base);

    let dot_product_trace = traces.get_mut(&Table::dot_product()).unwrap();
    fill_trace_dot_product(dot_product_trace, &memory_padded);

    traces.insert(
        Table::execution(),
        TableTrace {
            base: Vec::from(main_trace),
            ext: vec![],
            log_n_rows: log2_ceil_usize(n_cycles),
        },
    );
    for table in traces.keys().copied().collect::<Vec<_>>() {
        padd_table(&table, &mut traces);
    }

    ExecutionTrace {
        traces,
        public_memory_size: execution_result.public_memory_size,
        non_zero_memory_size: memory.0.len(),
        memory: memory_padded,
    }
}

fn padd_table(table: &Table, traces: &mut BTreeMap<Table, TableTrace>) {
    let trace = traces.get_mut(table).unwrap();
    let h = trace.base[0].len();
    trace
        .base
        .iter()
        .enumerate()
        .for_each(|(i, col)| assert_eq!(col.len(), h, "column {}, table {}", i, table.name()));

    trace.log_n_rows = log2_ceil_usize(h + 1).max(MIN_LOG_N_ROWS_PER_TABLE);
    let padding_len = (1 << trace.log_n_rows) - h;
    let padding_row_f = table.padding_row_f();
    trace.base.par_iter_mut().enumerate().for_each(|(i, col)| {
        col.extend(repeat_n(padding_row_f[i], padding_len));
    });

    let padding_row_ef = table.padding_row_ef();
    trace.ext.par_iter_mut().enumerate().for_each(|(i, col)| {
        col.extend(repeat_n(padding_row_ef[i], padding_len));
    });
}
