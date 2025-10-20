use std::mem::transmute;

use crate::instruction_encoder::field_representation;
use crate::{
    COL_INDEX_FP, COL_INDEX_MEM_ADDRESS_A, COL_INDEX_MEM_ADDRESS_B, COL_INDEX_MEM_ADDRESS_C,
    COL_INDEX_MEM_VALUE_A, COL_INDEX_MEM_VALUE_B, COL_INDEX_MEM_VALUE_C, COL_INDEX_PC,
    N_EXEC_COLUMNS, N_INSTRUCTION_COLUMNS,
};
use lean_vm::*;
use p3_field::Field;
use p3_field::PrimeCharacteristicRing;
use rayon::prelude::*;
use utils::{SyncUnsafeCell, ToUsize};

#[derive(Debug)]
pub struct ExecutionTrace {
    pub full_trace: Vec<Vec<F>>,
    pub n_poseidons_16: usize,
    pub n_poseidons_24: usize,
    pub poseidons_16: Vec<WitnessPoseidon16>, // padded with empty poseidons
    pub poseidons_24: Vec<WitnessPoseidon24>, // padded with empty poseidons
    pub dot_products: Vec<WitnessDotProduct>,
    pub multilinear_evals: Vec<WitnessMultilinearEval>,
    pub public_memory_size: usize,
    pub non_zero_memory_size: usize,
    pub memory: Vec<F>, // of length a multiple of public_memory_size
}

pub fn get_execution_trace(
    bytecode: &Bytecode,
    execution_result: ExecutionResult,
) -> ExecutionTrace {
    assert_eq!(execution_result.pcs.len(), execution_result.fps.len());
    let n_cycles = execution_result.pcs.len();
    let memory = &execution_result.memory;
    let log_n_cycles_rounded_up = n_cycles.next_power_of_two().ilog2() as usize;
    let trace = (0..N_INSTRUCTION_COLUMNS + N_EXEC_COLUMNS)
        .map(|_| unsafe { transmute(F::zero_vec(1 << log_n_cycles_rounded_up)) })
        .collect::<Vec<Vec<SyncUnsafeCell<F>>>>();

    execution_result
        .pcs
        .par_iter()
        .zip(execution_result.fps.par_iter())
        .enumerate()
        .for_each(|(cycle, (&pc, &fp))| {
            let instruction = &bytecode.instructions[pc];
            let field_repr = field_representation(instruction);

            let mut addr_a = F::ZERO;
            if field_repr[3].is_zero() {
                // flag_a == 0
                addr_a = F::from_usize(fp) + field_repr[0]; // fp + operand_a
            }
            let value_a = memory.0[addr_a.to_usize()].unwrap();
            let mut addr_b = F::ZERO;
            if field_repr[4].is_zero() {
                // flag_b == 0
                addr_b = F::from_usize(fp) + field_repr[1]; // fp + operand_b
            }
            let value_b = memory.0[addr_b.to_usize()].unwrap();

            let mut addr_c = F::ZERO;
            if field_repr[5].is_zero() {
                // flag_c == 0
                addr_c = F::from_usize(fp) + field_repr[2]; // fp + operand_c
            } else if let Instruction::Deref { shift_1, .. } = instruction {
                let operand_c = F::from_usize(*shift_1);
                assert_eq!(field_repr[2], operand_c); // debug purpose
                addr_c = value_a + operand_c;
            }
            let value_c = memory.0[addr_c.to_usize()].unwrap();

            unsafe {
                for (j, field) in field_repr.iter().enumerate() {
                    *trace[j][cycle].get() = *field;
                }
                *trace[COL_INDEX_MEM_VALUE_A][cycle].get() = value_a;
                *trace[COL_INDEX_MEM_VALUE_B][cycle].get() = value_b;
                *trace[COL_INDEX_MEM_VALUE_C][cycle].get() = value_c;
                *trace[COL_INDEX_PC][cycle].get() = F::from_usize(pc);
                *trace[COL_INDEX_FP][cycle].get() = F::from_usize(fp);
                *trace[COL_INDEX_MEM_ADDRESS_A][cycle].get() = addr_a;
                *trace[COL_INDEX_MEM_ADDRESS_B][cycle].get() = addr_b;
                *trace[COL_INDEX_MEM_ADDRESS_C][cycle].get() = addr_c;
            }
        });

    let mut trace: Vec<Vec<F>> = unsafe { transmute(trace) };

    // repeat the last row to get to a power of two
    trace.par_iter_mut().for_each(|column| {
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

    let n_poseidons_16 = execution_result.poseidons_16.len();
    let n_poseidons_24 = execution_result.poseidons_24.len();

    let ExecutionResult {
        mut poseidons_16,
        mut poseidons_24,
        dot_products,
        multilinear_evals,
        ..
    } = execution_result;

    poseidons_16.extend(vec![
        WitnessPoseidon16::poseidon_of_zero();
        n_poseidons_16.next_power_of_two() - n_poseidons_16
    ]);
    poseidons_24.extend(vec![
        WitnessPoseidon24::poseidon_of_zero();
        n_poseidons_24.next_power_of_two() - n_poseidons_24
    ]);

    ExecutionTrace {
        full_trace: trace,
        n_poseidons_16,
        n_poseidons_24,
        poseidons_16,
        poseidons_24,
        dot_products,
        multilinear_evals,
        public_memory_size: execution_result.public_memory_size,
        non_zero_memory_size: memory.0.len(),
        memory: memory_padded,
    }
}
