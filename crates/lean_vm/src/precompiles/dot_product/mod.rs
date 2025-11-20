use crate::precompiles::dot_product::vm_exec::exec_dot_product;
use crate::{
    Bus, BusDirection, BusSelector, ColIndex, EF, ExtensionFieldLookupIntoMemory, F,
    LookupIntoMemory, Memory, ModularPrecompile, PrecompileExecutionContext, PrecompileTrace,
    RunnerError, Table, VectorLookupIntoMemory,
};
use multilinear_toolkit::prelude::*;

mod air;
pub use air::*;

mod vm_exec;

#[derive(Debug)]
pub struct DotProductPrecompile;

impl ModularPrecompile for DotProductPrecompile {
    fn name() -> &'static str {
        "dot_product"
    }

    fn identifier() -> Table {
        Table::DotProduct
    }

    fn commited_columns_f() -> Vec<ColIndex> {
        vec![
            DOT_PRODUCT_AIR_COL_START_FLAG,
            DOT_PRODUCT_AIR_COL_LEN,
            DOT_PRODUCT_AIR_COL_INDEX_A,
            DOT_PRODUCT_AIR_COL_INDEX_B,
            DOT_PRODUCT_AIR_COL_INDEX_RES,
        ]
    }

    fn commited_columns_ef() -> Vec<ColIndex> {
        vec![DOT_PRODUCT_AIR_COL_COMPUTATION]
    }

    fn normal_lookups_f() -> Vec<LookupIntoMemory> {
        vec![]
    }

    fn normal_lookups_ef() -> Vec<ExtensionFieldLookupIntoMemory> {
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

    fn vector_lookups() -> Vec<VectorLookupIntoMemory> {
        vec![]
    }

    fn buses() -> Vec<Bus> {
        vec![Bus {
            table: Table::DotProduct,
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

    #[inline(always)]
    fn execute(
        arg_a: F,
        arg_b: F,
        arg_c: F,
        aux: usize,
        memory: &mut Memory,
        trace: &mut PrecompileTrace,
        _: PrecompileExecutionContext<'_>,
    ) -> Result<(), RunnerError> {
        exec_dot_product(arg_a, arg_b, arg_c, aux, memory, trace)
    }

    fn padding_row() -> Vec<EF> {
        [
            vec![
                EF::ONE, // StartFlag
                EF::ONE, // Len
            ],
            vec![EF::ZERO; DOT_PRODUCT_AIR_N_COLUMNS_TOTAL - 2],
        ]
        .concat()
    }
}
