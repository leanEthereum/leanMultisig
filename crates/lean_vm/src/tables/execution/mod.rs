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
        vec![
            DOT_PRODUCT_AIR_COL_START_FLAG,
            DOT_PRODUCT_AIR_COL_LEN,
            DOT_PRODUCT_AIR_COL_INDEX_A,
            DOT_PRODUCT_AIR_COL_INDEX_B,
            DOT_PRODUCT_AIR_COL_INDEX_RES,
        ]
    }

    fn commited_columns_ef(&self) -> Vec<ColIndex> {
        vec![DOT_PRODUCT_AIR_COL_COMPUTATION]
    }

    fn normal_lookups_f(&self) -> Vec<LookupIntoMemory> {
        vec![]
    }

    fn normal_lookups_ef(&self) -> Vec<ExtensionFieldLookupIntoMemory> {
        vec![
            ExtensionFieldLookupIntoMemory {
                index: DOT_PRODUCT_AIR_COL_INDEX_A,
                values: DOT_PRODUCT_AIR_COL_VALUE_A,
            },
            ExtensionFieldLookupIntoMemory {
                index: DOT_PRODUCT_AIR_COL_INDEX_B,
                values: DOT_PRODUCT_AIR_COL_VALUE_B,
            },
            ExtensionFieldLookupIntoMemory {
                index: DOT_PRODUCT_AIR_COL_INDEX_RES,
                values: DOT_PRODUCT_AIR_COL_VALUE_RES,
            },
        ]
    }

    fn vector_lookups(&self) -> Vec<VectorLookupIntoMemory> {
        vec![]
    }

    fn buses(&self) -> Vec<Bus> {
        vec![Bus {
            table: self.identifier(),
            direction: BusDirection::Pull,
            selector: BusSelector::Column(DOT_PRODUCT_AIR_COL_START_FLAG),
            data: vec![
                DOT_PRODUCT_AIR_COL_INDEX_A,
                DOT_PRODUCT_AIR_COL_INDEX_B,
                DOT_PRODUCT_AIR_COL_INDEX_RES,
                DOT_PRODUCT_AIR_COL_LEN,
            ],
        }]
    }

    fn padding_row(&self) -> Vec<EF> {
        let mut padding_row = vec![EF::ZERO; N_EXEC_AIR_COLUMNS];
        padding_row[COL_INDEX_JUMP] = EF::from_usize(1);
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
