use crate::*;
use multilinear_toolkit::prelude::*;

mod air;
pub use air::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExecutionTable;

impl TableT for ExecutionTable {
    fn name(&self) -> &'static str {
        "execution"
    }

    fn table(&self) -> Table {
        Table::execution()
    }

    fn is_execution_table(&self) -> bool {
        true
    }

    fn n_columns_f_total(&self) -> usize {
        N_EXEC_AIR_COLUMNS + N_TEMPORARY_EXEC_COLUMNS
    }

    fn lookups_f(&self) -> Vec<LookupIntoMemory> {
        vec![
            LookupIntoMemory {
                index: COL_INDEX_MEM_ADDRESS_A,
                values: vec![COL_INDEX_MEM_VALUE_A],
            },
            LookupIntoMemory {
                index: COL_INDEX_MEM_ADDRESS_B,
                values: vec![COL_INDEX_MEM_VALUE_B],
            },
            LookupIntoMemory {
                index: COL_INDEX_MEM_ADDRESS_C,
                values: vec![COL_INDEX_MEM_VALUE_C],
            },
        ]
    }

    fn lookups_ef(&self) -> Vec<ExtensionFieldLookupIntoMemory> {
        vec![]
    }

    fn bus(&self) -> Bus {
        Bus {
            table: BusTable::Variable(COL_INDEX_WHICH_PRECOMPILE),
            direction: BusDirection::Push,
            selector: COL_INDEX_IS_PRECOMPILE,
            data: vec![
                COL_INDEX_EXEC_NU_A,
                COL_INDEX_EXEC_NU_B,
                COL_INDEX_EXEC_NU_C,
                COL_INDEX_AUX_1,
                COL_INDEX_AUX_2,
            ],
        }
    }

    fn padding_row_f(&self) -> Vec<F> {
        let mut padding_row = vec![F::ZERO; N_EXEC_AIR_COLUMNS + N_TEMPORARY_EXEC_COLUMNS];
        padding_row[COL_INDEX_PC] = F::from_usize(ENDING_PC);
        padding_row[COL_INDEX_JUMP] = F::ONE;
        padding_row[COL_INDEX_FLAG_A] = F::ONE;
        padding_row[COL_INDEX_OPERAND_A] = F::ONE;
        padding_row[COL_INDEX_FLAG_B] = F::ONE;
        padding_row[COL_INDEX_FLAG_C] = F::ONE;
        padding_row[COL_INDEX_EXEC_NU_A] = F::ONE; // because at the end of program, we always jump (looping at pc=0, so condition = nu_a = 1)
        padding_row
    }

    fn padding_row_ef(&self) -> Vec<EF> {
        vec![]
    }

    #[inline(always)]
    fn execute(&self, _: F, _: F, _: F, _: usize, _: usize, _: &mut InstructionContext<'_>) -> Result<(), RunnerError> {
        unreachable!()
    }
}
