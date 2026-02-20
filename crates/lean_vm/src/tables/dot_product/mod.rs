use crate::{
    tables::dot_product::exec::{exec_dot_product_be, exec_dot_product_ee},
    *,
};
use backend::*;

mod air;
use air::*;
mod exec;
pub use exec::fill_trace_dot_product;

pub const DOT_PRODUCT_PRECOMPILE_DATA_BASE: usize = 0; // domain separation between Poseidon / DotProduct precompiles

/// Dot product between 2 vectors in the extension field EF.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DotProductPrecompile<const BUS: bool>; // BE = true for base-extension, false for extension-extension

impl<const BUS: bool> TableT for DotProductPrecompile<BUS> {
    fn name(&self) -> &'static str {
        "dot_product"
    }

    fn table(&self) -> Table {
        Table::dot_product()
    }

    fn lookups_f(&self) -> Vec<LookupIntoMemory> {
        vec![LookupIntoMemory {
            index: DOT_COL_A,
            values: vec![DOT_COL_VALUE_A_F],
        }]
    }

    fn lookups_ef(&self) -> Vec<ExtensionFieldLookupIntoMemory> {
        vec![
            ExtensionFieldLookupIntoMemory {
                index: DOT_COL_A,
                values: DOT_COL_VALUE_A_EF,
            },
            ExtensionFieldLookupIntoMemory {
                index: DOT_COL_B,
                values: DOT_COL_VALUE_B,
            },
            ExtensionFieldLookupIntoMemory {
                index: DOT_COL_RES,
                values: DOT_COL_VALUE_RES,
            },
        ]
    }

    fn bus(&self) -> Bus {
        Bus {
            direction: BusDirection::Pull,
            selector: DOT_COL_FLAG,
            data: vec![
                BusData::Column(DOT_COL_AUX),
                BusData::Column(DOT_COL_A),
                BusData::Column(DOT_COL_B),
                BusData::Column(DOT_COL_RES),
            ],
        }
    }

    fn n_columns_f_total(&self) -> usize {
        self.n_columns_f_air() + 1 // +1 for DOT_COL_AUX (non-AIR, used in bus logup)
    }

    fn padding_row_f(&self) -> Vec<F> {
        [
            vec![
                F::ZERO, // Is BE
                F::ZERO, // Flag
                F::ONE,  // Start
                F::ONE,  // Len
            ],
            vec![F::ZERO; self.n_columns_f_air() - 4], // A, B, RES, VALUE_A_F
            vec![F::from_usize(DOT_PRODUCT_PRECOMPILE_DATA_BASE + 4)], // Aux = BASE + 2*(0 + 2*1)
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
