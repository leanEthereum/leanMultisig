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

    fn identifier(&self) -> Table {
        Table::execution()
    }

    fn commited_columns_f(&self) -> Vec<ColIndex> {
        unreachable!()
    }

    fn commited_columns_ef(&self) -> Vec<ColIndex> {
        unreachable!()
    }

    fn normal_lookups_f(&self) -> Vec<LookupIntoMemory> {
        vec![]
    }

    fn normal_lookups_ef(&self) -> Vec<ExtensionFieldLookupIntoMemory> {
        unreachable!()
    }

    fn vector_lookups(&self) -> Vec<VectorLookupIntoMemory> {
        vec![]
    }

    fn buses(&self) -> Vec<Bus> {
        unreachable!()
    }

    fn padding_row(&self) -> Vec<EF> {
        let mut padding_row = vec![EF::ZERO; N_EXEC_AIR_COLUMNS];
        padding_row[COL_INDEX_PC] = EF::from_usize(ENDING_PC);
        padding_row[COL_INDEX_JUMP] = EF::ONE;
        padding_row[COL_INDEX_FLAG_A] = EF::ONE;
        padding_row[COL_INDEX_OPERAND_A] = EF::ONE;
        padding_row[COL_INDEX_FLAG_B] = EF::ONE;
        padding_row[COL_INDEX_FLAG_C] = EF::ONE;
        padding_row
    }

    #[inline(always)]
    fn execute(
        &self,
        _: F,
        _: F,
        _: F,
        _: usize,
        _: &mut InstructionContext<'_>,
    ) -> Result<(), RunnerError> {
        unreachable!()
    }
}
