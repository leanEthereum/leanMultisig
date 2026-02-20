use crate::*;
use backend::*;

mod air;
pub use air::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExecutionTable<const BUS: bool>;

impl<const BUS: bool> TableT for ExecutionTable<BUS> {
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
        N_TOTAL_EXECUTION_COLUMNS + N_TEMPORARY_EXEC_COLUMNS
    }

    fn lookups_f(&self) -> Vec<LookupIntoMemory> {
        vec![
            LookupIntoMemory {
                index: COL_MEM_ADDRESS_A,
                values: vec![COL_MEM_VALUE_A],
            },
            LookupIntoMemory {
                index: COL_MEM_ADDRESS_B,
                values: vec![COL_MEM_VALUE_B],
            },
            LookupIntoMemory {
                index: COL_MEM_ADDRESS_C,
                values: vec![COL_MEM_VALUE_C],
            },
        ]
    }

    fn lookups_ef(&self) -> Vec<ExtensionFieldLookupIntoMemory> {
        vec![]
    }

    fn bus(&self) -> Bus {
        Bus {
            direction: BusDirection::Push,
            selector: COL_IS_PRECOMPILE,
            data: vec![
                BusData::Column(COL_PRECOMPILE_DATA),
                BusData::Column(COL_EXEC_NU_A),
                BusData::Column(COL_EXEC_NU_B),
                BusData::Column(COL_EXEC_NU_C),
            ],
        }
    }

    fn padding_row_f(&self) -> Vec<F> {
        let mut padding_row = vec![F::ZERO; N_TOTAL_EXECUTION_COLUMNS + N_TEMPORARY_EXEC_COLUMNS];
        padding_row[COL_PC] = F::from_usize(ENDING_PC);
        padding_row[COL_JUMP] = F::ONE;
        padding_row[COL_FLAG_A] = F::ONE;
        padding_row[COL_OPERAND_A] = F::ONE;
        padding_row[COL_FLAG_B] = F::ONE;
        padding_row[COL_FLAG_C_FP] = F::ONE; // this is kind of arbitrary
        padding_row[COL_EXEC_NU_A] = F::ONE; // because at the end of program, we always jump (looping at pc=0, so condition = nu_a = 1)
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
