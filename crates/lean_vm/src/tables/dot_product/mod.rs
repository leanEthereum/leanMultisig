use crate::tables::dot_product::exec::exec_dot_product;
use crate::*;
use multilinear_toolkit::prelude::*;

mod air;
pub use air::*;

mod exec;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DotProductPrecompile;

impl TableT for DotProductPrecompile {
    fn name(&self) -> &'static str {
        "dot_product"
    }

    fn identifier(&self) -> Table {
        Table::dot_product()
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
            selector: DOT_PRODUCT_AIR_COL_START_FLAG,
            data: vec![
                DOT_PRODUCT_AIR_COL_INDEX_A,
                DOT_PRODUCT_AIR_COL_INDEX_B,
                DOT_PRODUCT_AIR_COL_INDEX_RES,
                DOT_PRODUCT_AIR_COL_LEN,
            ],
        }]
    }

    fn padding_row_f(&self) -> Vec<F> {
        [
            vec![
                F::ONE, // StartFlag
                F::ONE, // Len
            ],
            vec![F::ZERO; DOT_PRODUCT_AIR_N_COLUMNS_F - 2],
        ]
        .concat()
    }

    fn padding_row_ef(&self) -> Vec<EF> {
        vec![EF::ZERO; DOT_PRODUCT_AIR_N_COLUMNS_EF]
    }

    #[inline(always)]
    fn execute(
        &self,
        arg_a: F,
        arg_b: F,
        arg_c: F,
        aux: usize,
        ctx: &mut InstructionContext<'_>,
    ) -> Result<(), RunnerError> {
        let trace = &mut ctx.precompile_traces[self.identifier().index()];
        exec_dot_product(arg_a, arg_b, arg_c, aux, ctx.memory, trace)
    }
}
