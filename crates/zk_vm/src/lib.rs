use std::ops::Range;

use compiler::{PRECOMPILES, compile_program};
use vm::execute_bytecode;

mod air;
mod common;
mod dot_product_air;
mod execution_trace;
mod instruction_encoder;
mod poseidon_tables;
pub mod prove_execution;
pub mod verify_execution;

#[cfg(test)]
pub mod recursion;

const UNIVARIATE_SKIPS: usize = 4;

const N_INSTRUCTION_COLUMNS: usize = 15;
const N_COMMITTED_EXEC_COLUMNS: usize = 5;
const N_MEMORY_VALUE_COLUMNS: usize = 3; // virtual (lookup into memory, with logup*)
const N_EXEC_COLUMNS: usize = N_COMMITTED_EXEC_COLUMNS + N_MEMORY_VALUE_COLUMNS;
const N_INSTRUCTION_COLUMNS_IN_AIR: usize = N_INSTRUCTION_COLUMNS - PRECOMPILES.len();
const N_EXEC_AIR_COLUMNS: usize = N_INSTRUCTION_COLUMNS_IN_AIR + N_EXEC_COLUMNS;
const N_TOTAL_COLUMNS: usize = N_INSTRUCTION_COLUMNS + N_EXEC_COLUMNS;

// Instruction columns
const COL_INDEX_OPERAND_A: usize = 0;
const COL_INDEX_OPERAND_B: usize = 1;
const COL_INDEX_OPERAND_C: usize = 2;
const COL_INDEX_FLAG_A: usize = 3;
const COL_INDEX_FLAG_B: usize = 4;
const COL_INDEX_FLAG_C: usize = 5;
const COL_INDEX_ADD: usize = 6;
const COL_INDEX_MUL: usize = 7;
const COL_INDEX_DEREF: usize = 8;
const COL_INDEX_JUZ: usize = 9;
const COL_INDEX_AUX: usize = 10;
const COL_INDEX_POSEIDON_16: usize = 11;
const COL_INDEX_POSEIDON_24: usize = 12;
const COL_INDEX_DOT_PRODUCT: usize = 13;
const COL_INDEX_MULTILINEAR_EVAL: usize = 14;

// Execution columns
const COL_INDEX_MEM_VALUE_A: usize = 15; // virtual with logup*
const COL_INDEX_MEM_VALUE_B: usize = 16; // virtual with logup*
const COL_INDEX_MEM_VALUE_C: usize = 17; // virtual with logup*
const COL_INDEX_PC: usize = 18;
const COL_INDEX_FP: usize = 19;
const COL_INDEX_MEM_ADDRESS_A: usize = 20;
const COL_INDEX_MEM_ADDRESS_B: usize = 21;
const COL_INDEX_MEM_ADDRESS_C: usize = 22;

fn exec_column_groups() -> Vec<Range<usize>> {
    [
        (0..N_INSTRUCTION_COLUMNS_IN_AIR)
            .map(|i| i..i + 1)
            .collect::<Vec<_>>(),
        vec![
            N_INSTRUCTION_COLUMNS_IN_AIR..N_INSTRUCTION_COLUMNS_IN_AIR + N_MEMORY_VALUE_COLUMNS,
            N_INSTRUCTION_COLUMNS_IN_AIR + N_MEMORY_VALUE_COLUMNS
                ..N_INSTRUCTION_COLUMNS_IN_AIR + N_MEMORY_VALUE_COLUMNS + 1, // pc
            N_INSTRUCTION_COLUMNS_IN_AIR + N_MEMORY_VALUE_COLUMNS + 1
                ..N_INSTRUCTION_COLUMNS_IN_AIR + N_MEMORY_VALUE_COLUMNS + 2, // fp
            N_INSTRUCTION_COLUMNS_IN_AIR + N_MEMORY_VALUE_COLUMNS + 2
                ..N_INSTRUCTION_COLUMNS_IN_AIR + N_MEMORY_VALUE_COLUMNS + N_COMMITTED_EXEC_COLUMNS,
        ],
    ]
    .concat()
}

pub fn compile_and_run(program: &str, public_input: &[vm::F], private_input: &[vm::F]) {
    let bytecode = compile_program(program);
    execute_bytecode(&bytecode, &public_input, private_input);
}

pub trait InAirColumnIndex {
    fn index_in_air(self) -> usize;
}

impl InAirColumnIndex for usize {
    fn index_in_air(self) -> usize {
        if self < N_INSTRUCTION_COLUMNS_IN_AIR {
            self
        } else {
            assert!(self >= N_INSTRUCTION_COLUMNS);
            assert!(self < N_INSTRUCTION_COLUMNS + N_EXEC_COLUMNS);
            self - PRECOMPILES.len()
        }
    }
}
