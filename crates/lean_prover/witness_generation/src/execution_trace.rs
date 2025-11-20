use crate::instruction_encoder::field_representation;
use crate::*;
use lean_vm::*;
use multilinear_toolkit::prelude::*;
use p3_air::Air;
use std::{array, iter::repeat_n};
use utils::{ToUsize, transposed_par_iter_mut};
use vm_air::*;

#[derive(Debug)]
pub struct ExecutionTrace {
    pub full_trace: [Vec<F>; N_EXEC_AIR_COLUMNS],
    pub nu_columns: [Vec<F>; 3],
    pub n_cycles: usize, // before padding with the repeated final instruction
    pub n_compressions_16: usize,
    pub poseidons_16: PrecompileTrace, // padded with empty poseidons
    pub poseidons_24: PrecompileTrace, // padded with empty poseidons
    pub dot_products: PrecompileTrace,
    pub multilinear_evals: PrecompileTrace,
    pub multilinear_evals_witness: Vec<WitnessMultilinearEval>,
    pub public_memory_size: usize,
    pub non_zero_memory_size: usize,
    pub memory: Vec<F>, // of length a multiple of public_memory_size
}

pub fn get_execution_trace(
    bytecode: &Bytecode,
    mut execution_result: ExecutionResult,
) -> ExecutionTrace {
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
    let mut trace: [Vec<F>; N_EXEC_AIR_COLUMNS] =
        array::from_fn(|_| F::zero_vec(n_cycles.next_power_of_two()));
    let mut nu_columns: [Vec<F>; 3] = array::from_fn(|_| F::zero_vec(n_cycles.next_power_of_two()));

    transposed_par_iter_mut(&mut trace)
        .zip(transposed_par_iter_mut(&mut nu_columns))
        .zip(execution_result.pcs.par_iter())
        .zip(execution_result.fps.par_iter())
        .for_each(|(((trace_row, nu_row), &pc), &fp)| {
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
            let nu_c = field_repr[COL_INDEX_FLAG_C] * F::from_usize(fp)
                + (F::ONE - field_repr[COL_INDEX_FLAG_C]) * value_c;
            *nu_row[0] = nu_a;
            *nu_row[1] = nu_b;
            *nu_row[2] = nu_c;

            *trace_row[COL_INDEX_MEM_VALUE_A] = value_a;
            *trace_row[COL_INDEX_MEM_VALUE_B] = value_b;
            *trace_row[COL_INDEX_MEM_VALUE_C] = value_c;
            *trace_row[COL_INDEX_PC] = F::from_usize(pc);
            *trace_row[COL_INDEX_FP] = F::from_usize(fp);
            *trace_row[COL_INDEX_MEM_ADDRESS_A] = addr_a;
            *trace_row[COL_INDEX_MEM_ADDRESS_B] = addr_b;
            *trace_row[COL_INDEX_MEM_ADDRESS_C] = addr_c;
        });

    // repeat the last row to get to a power of two
    trace.par_iter_mut().for_each(|column| {
        let last_value = column[n_cycles - 1];
        for cell in &mut column[n_cycles..] {
            *cell = last_value;
        }
    });
    nu_columns.par_iter_mut().for_each(|column| {
        let last_value = column[n_cycles - 1];
        for cell in &mut column[n_cycles..] {
            *cell = last_value;
        }
    });

    let mut memory_padded = memory
        .0
        .par_iter()
        .map(|&v| v.unwrap_or(F::ZERO))
        .collect::<Vec<F>>();
    memory_padded.resize(memory.0.len().next_power_of_two(), F::ZERO);

    let ExecutionResult {
        mut poseidons_16,
        mut poseidons_24,
        mut dot_products,
        multilinear_evals,
        multilinear_evals_witness,
        ..
    } = execution_result;

    padd_precompile_table::<DotProductPrecompile>(&mut dot_products);
    padd_precompile_table::<Poseidon16Precompile>(&mut poseidons_16);
    padd_precompile_table::<Poseidon24Precompile>(&mut poseidons_24);

    let n_compressions_16;
    (poseidons_16, n_compressions_16) = put_poseidon16_compressions_at_the_end(&poseidons_16); // TODO avoid reallocation

    ExecutionTrace {
        full_trace: trace,
        nu_columns,
        n_cycles,
        n_compressions_16,
        poseidons_16,
        poseidons_24,
        dot_products,
        multilinear_evals,
        multilinear_evals_witness,
        public_memory_size: execution_result.public_memory_size,
        non_zero_memory_size: memory.0.len(),
        memory: memory_padded,
    }
}

fn put_poseidon16_compressions_at_the_end(
    poseidons_16: &PrecompileTrace,
) -> (PrecompileTrace, usize) {
    let n = poseidons_16.base[0].len();
    assert_eq!(Poseidon16Precompile::n_columns_f(), poseidons_16.base.len());
    assert_eq!(poseidons_16.ext.len(), 0);
    let mut new_trace = vec![Vec::with_capacity(n); Poseidon16Precompile::n_columns_f()];
    // TODO parallelize
    for row in 0..n {
        if poseidons_16.base[POSEIDON_16_COL_INDEX_COMPRESSION][row] == F::from_bool(false) {
            for col in 0..Poseidon16Precompile::n_columns_f() {
                new_trace[col].push(poseidons_16.base[col][row]);
            }
        }
    }
    let mut n_compressions = 0;
    for row in 0..n {
        if poseidons_16.base[POSEIDON_16_COL_INDEX_COMPRESSION][row] == F::from_bool(true) {
            n_compressions += 1;
            for col in 0..Poseidon16Precompile::n_columns_f() {
                new_trace[col].push(poseidons_16.base[col][row]);
            }
        }
    }

    (
        PrecompileTrace {
            base: new_trace,
            ext: vec![],
            padding_len: poseidons_16.padding_len,
        },
        n_compressions,
    )
}

fn padd_precompile_table<P: ModularPrecompile>(trace: &mut PrecompileTrace) {
    trace.padding_len = trace.base[0]
        .len()
        .next_power_of_two()
        .max(MIN_N_ROWS_PER_TABLE)
        - trace.base[0].len();
    for (i, col) in trace.base.iter_mut().enumerate() {
        let default_value: F = P::padding_row()[i].as_base().unwrap();
        col.extend(repeat_n(default_value, trace.padding_len));
    }
    for (i, col) in trace.ext.iter_mut().enumerate() {
        let default_value = P::padding_row()[i + P::n_columns_f()];
        col.extend(repeat_n(default_value, trace.padding_len));
    }
}
