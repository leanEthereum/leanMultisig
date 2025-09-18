#![cfg_attr(not(test), allow(unused_crate_dependencies))]

use lean_compiler::PRECOMPILES;

mod execution_trace;
mod instruction_encoder;

pub use execution_trace::*;
pub use instruction_encoder::*;

mod poseidon_tables;
pub use poseidon_tables::*;

pub const N_INSTRUCTION_COLUMNS: usize = 15;
pub const N_COMMITTED_EXEC_COLUMNS: usize = 5;
pub const N_MEMORY_VALUE_COLUMNS: usize = 3; // virtual (lookup into memory, with logup*)
pub const N_EXEC_COLUMNS: usize = N_COMMITTED_EXEC_COLUMNS + N_MEMORY_VALUE_COLUMNS;
pub const N_INSTRUCTION_COLUMNS_IN_AIR: usize = N_INSTRUCTION_COLUMNS - PRECOMPILES.len();
pub const N_EXEC_AIR_COLUMNS: usize = N_INSTRUCTION_COLUMNS_IN_AIR + N_EXEC_COLUMNS;
pub const N_TOTAL_COLUMNS: usize = N_INSTRUCTION_COLUMNS + N_EXEC_COLUMNS;

// Instruction columns
pub const COL_INDEX_OPERAND_A: usize = 0;
pub const COL_INDEX_OPERAND_B: usize = 1;
pub const COL_INDEX_OPERAND_C: usize = 2;
pub const COL_INDEX_FLAG_A: usize = 3;
pub const COL_INDEX_FLAG_B: usize = 4;
pub const COL_INDEX_FLAG_C: usize = 5;
pub const COL_INDEX_ADD: usize = 6;
pub const COL_INDEX_MUL: usize = 7;
pub const COL_INDEX_DEREF: usize = 8;
pub const COL_INDEX_JUMP: usize = 9;
pub const COL_INDEX_AUX: usize = 10;
pub const COL_INDEX_POSEIDON_16: usize = 11;
pub const COL_INDEX_POSEIDON_24: usize = 12;
pub const COL_INDEX_DOT_PRODUCT: usize = 13;
pub const COL_INDEX_MULTILINEAR_EVAL: usize = 14;

// Execution columns
pub const COL_INDEX_MEM_VALUE_A: usize = 15; // virtual with logup*
pub const COL_INDEX_MEM_VALUE_B: usize = 16; // virtual with logup*
pub const COL_INDEX_MEM_VALUE_C: usize = 17; // virtual with logup*
pub const COL_INDEX_PC: usize = 18;
pub const COL_INDEX_FP: usize = 19;
pub const COL_INDEX_MEM_ADDRESS_A: usize = 20;
pub const COL_INDEX_MEM_ADDRESS_B: usize = 21;
pub const COL_INDEX_MEM_ADDRESS_C: usize = 22;

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
