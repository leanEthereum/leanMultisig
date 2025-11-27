use crate::{InstructionContext, tables::eq_poly_base_ext::exec::exec_eq_poly_base_ext, *};
use multilinear_toolkit::prelude::*;

mod air;
use air::*;
mod exec;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EqPolyBaseExtPrecompile;

impl TableT for EqPolyBaseExtPrecompile {
    fn name(&self) -> &'static str {
        "eq_poly_base_ext"
    }

    fn identifier(&self) -> Table {
        Table::eq_poly_base_ext()
    }

    fn commited_columns_f(&self) -> Vec<ColIndex> {
        vec![COL_FLAG, COL_LEN, COL_INDEX_A, COL_INDEX_B, COL_INDEX_RES]
    }

    fn commited_columns_ef(&self) -> Vec<ColIndex> {
        vec![COL_COMPUTATION]
    }

    fn normal_lookups_f(&self) -> Vec<LookupIntoMemory> {
        vec![LookupIntoMemory {
            index: COL_INDEX_A,
            values: COL_VALUE_A,
        }]
    }

    fn normal_lookups_ef(&self) -> Vec<ExtensionFieldLookupIntoMemory> {
        vec![
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

    fn vector_lookups(&self) -> Vec<VectorLookupIntoMemory> {
        vec![]
    }

    fn buses(&self) -> Vec<Bus> {
        vec![Bus {
            table: BusTable::Constant(self.identifier()),
            direction: BusDirection::Pull,
            selector: COL_FLAG,
            data: vec![COL_INDEX_A, COL_INDEX_B, COL_INDEX_RES, COL_LEN],
        }]
    }

    fn padding_row_f(&self) -> Vec<F> {
        [vec![
            F::ONE,                                  // StartFlag
            F::ONE,                                  // Len
            F::ZERO,                                 // Index A
            F::ZERO,                                 // Index B
            F::from_usize(ONE_VEC_PTR * VECTOR_LEN), // Index Res
            F::ZERO,                                 // Value A
        ]]
        .concat()
    }

    fn padding_row_ef(&self) -> Vec<EF> {
        vec![
            EF::ZERO, // Value B
            EF::ONE,  // Value Res
            EF::ONE,  // Computation
        ]
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
        exec_eq_poly_base_ext(arg_a, arg_b, arg_c, aux, &mut ctx.memory, trace)
    }
}
