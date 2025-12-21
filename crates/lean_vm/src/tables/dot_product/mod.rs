use crate::{
    tables::dot_product::exec::{exec_dot_product_be, exec_dot_product_ee},
    *,
};
use multilinear_toolkit::prelude::*;

mod air;
use air::*;
mod exec;
pub use exec::fill_trace_dot_product;

/// Dot product between 2 vectors in the extension field EF.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DotProductPrecompile; // BE = true for base-extension, false for extension-extension

impl TableT for DotProductPrecompile {
    fn name(&self) -> &'static str {
        "dot_product"
    }

    fn table(&self) -> Table {
        Table::dot_product()
    }

    fn lookups_f(&self) -> Vec<LookupIntoMemory> {
        vec![LookupIntoMemory {
            index: COL_INDEX_A,
            values: vec![COL_VALUE_A_F],
        }]
    }

    fn lookups_ef(&self) -> Vec<ExtensionFieldLookupIntoMemory> {
        vec![
            ExtensionFieldLookupIntoMemory {
                index: COL_INDEX_A,
                values: COL_VALUE_A_EF,
            },
            ExtensionFieldLookupIntoMemory {
                index: COL_INDEX_B,
                values: COL_VALUE_B,
            },
            ExtensionFieldLookupIntoMemory {
                index: COL_INDEX_RES,
                values: COL_VALUE_RES,
            },
        ]
    }

    fn buses(&self) -> Vec<Bus> {
        vec![Bus {
            table: BusTable::Constant(self.table()),
            direction: BusDirection::Pull,
            selector: COL_FLAG,
            data: vec![COL_INDEX_A, COL_INDEX_B, COL_INDEX_RES, COL_LEN, COL_IS_BE],
        }]
    }

    fn padding_row_f(&self) -> Vec<F> {
        [
            vec![
                F::ZERO, // Is BE
                F::ZERO, // Flag
                F::ONE,  // Start
                F::ONE,  // Len
            ],
            vec![F::ZERO; self.n_columns_f_air() - 4],
        ]
        .concat()
    }

    fn padding_row_ef(&self) -> Vec<EF> {
        vec![EF::ZERO; self.n_columns_ef_air()]
    }

    #[inline(always)]
    fn execute(
        &self,
        arg_a: F,
        arg_b: F,
        arg_c: F,
        size: usize,
        is_be: usize,
        ctx: &mut InstructionContext<'_>,
    ) -> Result<(), RunnerError> {
        assert!(is_be == 0 || is_be == 1);
        let is_be = is_be == 1;
        let trace = ctx.traces.get_mut(&self.table()).unwrap();
        if is_be {
            exec_dot_product_be(arg_a, arg_b, arg_c, size, ctx.memory, trace)
        } else {
            exec_dot_product_ee(arg_a, arg_b, arg_c, size, ctx.memory, trace)
        }
    }
}
