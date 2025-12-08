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

pub fn get_execution_trace(bytecode: &Bytecode, mut execution_result: ExecutionResult) -> ExecutionTrace {
    assert_eq!(execution_result.pcs.len(), execution_result.fps.len());

    // padding to make proof work even on small programs (TODO make this more elegant)
    let min_cycles = 32 << MIN_LOG_N_ROWS_PER_TABLE;
    if execution_result.pcs.len() < min_cycles {
        execution_result
            .pcs
            .resize(min_cycles, *execution_result.pcs.last().unwrap());
        execution_result
            .fps
            .resize(min_cycles, *execution_result.fps.last().unwrap());
    }

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
            if field_repr[COL_INDEX_FLAG_A].is_zero() {
                // flag_a == 0
                addr_a = F::from_usize(fp) + field_repr[0]; // fp + operand_a
            }
            let value_a = memory.0[addr_a.to_usize()].unwrap();
            let mut addr_b = F::ZERO;
            if field_repr[COL_INDEX_FLAG_B].is_zero() {
                // flag_b == 0
                addr_b = F::from_usize(fp) + field_repr[1]; // fp + operand_b
            }
            let value_b = memory.0[addr_b.to_usize()].unwrap();

            let mut addr_c = F::ZERO;
            if field_repr[COL_INDEX_FLAG_C].is_zero() {
                // flag_c == 0
                addr_c = F::from_usize(fp) + field_repr[2]; // fp + operand_c
            } else if let Instruction::Deref { shift_1, .. } = instruction {
                let operand_c = F::from_usize(*shift_1);
                assert_eq!(field_repr[2], operand_c); // debug purpose
                addr_c = value_a + operand_c;
            }
            let value_c = memory.0[addr_c.to_usize()].unwrap();

            for (j, field) in field_repr.iter().enumerate() {
                *trace_row[j] = *field;
            }

            let nu_a = field_repr[COL_INDEX_FLAG_A] * field_repr[COL_INDEX_OPERAND_A]
                + (F::ONE - field_repr[COL_INDEX_FLAG_A]) * value_a;
            let nu_b = field_repr[COL_INDEX_FLAG_B] * field_repr[COL_INDEX_OPERAND_B]
                + (F::ONE - field_repr[COL_INDEX_FLAG_B]) * value_b;
            let nu_c =
                field_repr[COL_INDEX_FLAG_C] * F::from_usize(fp) + (F::ONE - field_repr[COL_INDEX_FLAG_C]) * value_c;
            *trace_row[COL_INDEX_EXEC_NU_A] = nu_a;
            *trace_row[COL_INDEX_EXEC_NU_B] = nu_b;
            *trace_row[COL_INDEX_EXEC_NU_C] = nu_c;

            *trace_row[COL_INDEX_MEM_VALUE_A] = value_a;
            *trace_row[COL_INDEX_MEM_VALUE_B] = value_b;
            *trace_row[COL_INDEX_MEM_VALUE_C] = value_c;
            *trace_row[COL_INDEX_PC] = F::from_usize(pc);
            *trace_row[COL_INDEX_FP] = F::from_usize(fp);
            *trace_row[COL_INDEX_MEM_ADDRESS_A] = addr_a;
            *trace_row[COL_INDEX_MEM_ADDRESS_B] = addr_b;
            *trace_row[COL_INDEX_MEM_ADDRESS_C] = addr_c;
        });

    let mut memory_padded = memory.0.par_iter().map(|&v| v.unwrap_or(F::ZERO)).collect::<Vec<F>>();
    memory_padded.resize(memory.0.len().next_power_of_two(), F::ZERO);

    let ExecutionResult { mut traces, .. } = execution_result;

    // TODO avoid reallocation
    let poseidon_trace = traces.get_mut(&Table::poseidon16()).unwrap();
    let completed_poseidon_trace = generate_trace_poseidon_16(
        &std::array::from_fn(|i| std::mem::take(&mut poseidon_trace.base[POSEIDON_16_COL_INPUT_START + i])),
        &std::mem::take(&mut poseidon_trace.base[POSEIDON_16_COL_INDEX_A]),
        &std::mem::take(&mut poseidon_trace.base[POSEIDON_16_COL_INDEX_B]),
        &std::mem::take(&mut poseidon_trace.base[POSEIDON_16_COL_INDEX_RES]),
        &std::mem::take(&mut poseidon_trace.base[POSEIDON_16_COL_COMPRESSION]),
    );
    poseidon_trace.base = completed_poseidon_trace;

    traces.insert(
        Table::execution(),
        TableTrace {
            base: Vec::from(main_trace),
            ext: vec![],
            height: Default::default(),
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

    trace.height = TableHeight(h);
    let padding_len = trace.height.padding_len();
    let padding_row_f = table.padding_row_f();
    trace.base.par_iter_mut().enumerate().for_each(|(i, col)| {
        col.extend(repeat_n(padding_row_f[i], padding_len));
    });

    let padding_row_ef = table.padding_row_ef();
    trace.ext.par_iter_mut().enumerate().for_each(|(i, col)| {
        col.extend(repeat_n(padding_row_ef[i], padding_len));
    });
}
