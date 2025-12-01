use crate::{
    tables::dot_product::exec::{exec_dot_product_be, exec_dot_product_ee},
    *,
};
use multilinear_toolkit::prelude::*;

mod air;
use air::*;
mod exec;

/// Dot product between 2 vectors in the extension field EF.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DotProductPrecompile<const BE: bool>; // BE = true for base-extension, false for extension-extension

impl<const BE: bool> TableT for DotProductPrecompile<BE> {
    fn name(&self) -> &'static str {
        if BE { "dot_product_be" } else { "dot_product_ee" }
    }

    fn identifier(&self) -> Table {
        if BE {
            Table::dot_product_be()
        } else {
            Table::dot_product_ee()
        }
    }

    fn commited_columns_f(&self) -> Vec<ColIndex> {
        vec![COL_FLAG, COL_LEN, COL_INDEX_A, COL_INDEX_B, COL_INDEX_RES]
    }

    fn commited_columns_ef(&self) -> Vec<ColIndex> {
        vec![COL_COMPUTATION]
    }

    fn normal_lookups_f(&self) -> Vec<LookupIntoMemory> {
        if BE {
            vec![LookupIntoMemory {
                index: COL_INDEX_A,
                values: dot_product_air_col_value_a(BE),
            }]
        } else {
            vec![]
        }
    }

    fn normal_lookups_ef(&self) -> Vec<ExtensionFieldLookupIntoMemory> {
        let mut res = vec![
            ExtensionFieldLookupIntoMemory {
                index: COL_INDEX_B,
                values: COL_VALUE_B,
            },
            ExtensionFieldLookupIntoMemory {
                index: COL_INDEX_RES,
                values: COL_VALUE_RES,
            },
        ];
        if !BE {
            res.insert(
                0,
                ExtensionFieldLookupIntoMemory {
                    index: COL_INDEX_A,
                    values: dot_product_air_col_value_a(BE),
                },
            );
        }
        res
    }

    fn vector_lookups(&self) -> Vec<VectorLookupIntoMemory> {
        vec![]
    }

    fn buses(&self) -> Vec<Bus> {
        vec![Bus {
            table: BusTable::Constant(self.identifier()),
            direction: BusDirection::Pull,
            selector: BusSelector::Column(COL_FLAG),
            data: vec![COL_INDEX_A, COL_INDEX_B, COL_INDEX_RES, COL_LEN],
            degree: 1,
        }]
    }

    fn padding_row_f(&self) -> Vec<F> {
        [
            vec![
                F::ONE, // StartFlag
                F::ONE, // Len
            ],
            vec![F::ZERO; dot_product_air_n_cols_f(BE) - 2],
        ]
        .concat()
    }

    fn padding_row_ef(&self) -> Vec<EF> {
        vec![EF::ZERO; dot_product_air_n_cols_ef(BE)]
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
        let trace = ctx.traces.get_mut(&self.identifier()).unwrap();
        if BE {
            exec_dot_product_be(arg_a, arg_b, arg_c, aux, ctx.memory, trace)
        } else {
            exec_dot_product_ee(arg_a, arg_b, arg_c, aux, ctx.memory, trace)
        }
    }
}
