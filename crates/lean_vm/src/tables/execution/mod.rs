use crate::execution::memory::MemoryAccess;
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

    fn n_columns_total(&self) -> usize {
        N_TOTAL_EXECUTION_COLUMNS + N_TEMPORARY_EXEC_COLUMNS
    }

    fn lookups(&self) -> Vec<LookupIntoMemory> {
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

    #[allow(clippy::vec_init_then_push)] // https://github.com/leanEthereum/leanMultisig/issues/198
    fn bus(&self) -> Bus {
        let mut data = Vec::with_capacity(4);
        data.push(BusData::Column(COL_PRECOMPILE_DATA));
        data.push(BusData::Column(COL_EXEC_NU_A));
        data.push(BusData::Column(COL_EXEC_NU_B));
        data.push(BusData::Column(COL_EXEC_NU_C));
        Bus {
            direction: BusDirection::Push,
            selector: COL_IS_PRECOMPILE,
            data,
        }
    }

    fn padding_row(&self, zero_vec_ptr: usize, _null_hash_ptr: usize) -> Vec<F> {
        let mut padding_row = vec![F::ZERO; N_TOTAL_EXECUTION_COLUMNS + N_TEMPORARY_EXEC_COLUMNS];
        padding_row[COL_PC] = F::from_usize(ENDING_PC);
        padding_row[COL_JUMP] = F::ONE;
        padding_row[COL_FLAG_A] = F::ONE;
        padding_row[COL_OPERAND_A] = F::ONE;
        padding_row[COL_FLAG_B] = F::ONE;
        padding_row[COL_FLAG_C_FP] = F::ONE; // this is kind of arbitrary
        padding_row[COL_EXEC_NU_A] = F::ONE; // because at the end of program, we always jump (looping at pc=0, so condition = nu_a = 1)
        padding_row[COL_MEM_ADDRESS_A] = F::from_usize(zero_vec_ptr);
        padding_row[COL_MEM_ADDRESS_B] = F::from_usize(zero_vec_ptr);
        padding_row[COL_MEM_ADDRESS_C] = F::from_usize(zero_vec_ptr);
        padding_row
    }

    #[inline(always)]
    fn execute<M: MemoryAccess>(
        &self,
        _: F,
        _: F,
        _: F,
        _: PrecompileCompTimeArgs<usize>,
        _: &mut InstructionContext<'_, M>,
    ) -> Result<(), RunnerError> {
        unreachable!()
    }
}
