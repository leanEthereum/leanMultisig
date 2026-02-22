use crate::{
    tables::extension_op::exec::{
        exec_add_be, exec_add_ee, exec_mul_be, exec_mul_ee, exec_poly_eq_be, exec_poly_eq_ee,
    },
    *,
};
use backend::*;

mod air;
use air::*;
mod exec;
pub use exec::fill_trace_extension_op;

/// Extension field operation: ADD, MUL, or POLY_EQ on extension field elements.
/// Operand A can be either a direct base field value (BE) or a pointer to EF element (EE).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExtensionOpPrecompile<const BUS: bool>;

impl<const BUS: bool> TableT for ExtensionOpPrecompile<BUS> {
    fn name(&self) -> &'static str {
        "extension_op"
    }

    fn table(&self) -> Table {
        Table::extension_op()
    }

    fn lookups_f(&self) -> Vec<LookupIntoMemory> {
        vec![LookupIntoMemory {
            index: EXT_COL_ARG_A,
            values: vec![EXT_COL_VALUE_A_F],
        }]
    }

    fn lookups_ef(&self) -> Vec<ExtensionFieldLookupIntoMemory> {
        vec![
            ExtensionFieldLookupIntoMemory {
                index: EXT_COL_ARG_A,
                values: EXT_COL_VALUE_A_EF,
            },
            ExtensionFieldLookupIntoMemory {
                index: EXT_COL_IDX_B,
                values: EXT_COL_VALUE_B,
            },
            ExtensionFieldLookupIntoMemory {
                index: EXT_COL_IDX_R,
                values: EXT_COL_VALUE_RES,
            },
        ]
    }

    fn bus(&self) -> Bus {
        Bus {
            direction: BusDirection::Pull,
            selector: EXT_COL_FLAG,
            data: vec![
                BusData::Column(EXT_COL_AUX),
                BusData::Column(EXT_COL_ARG_A),
                BusData::Column(EXT_COL_IDX_B),
                BusData::Column(EXT_COL_IDX_R),
            ],
        }
    }

    fn n_columns_f_total(&self) -> usize {
        self.n_columns_f_air() + 1 // +1 for EXT_COL_AUX (non-AIR, used in bus logup)
    }

    fn padding_row_f(&self) -> Vec<F> {
        // All zeros: is_be=0, flag=0, flag_add=0, flag_mul=0, flag_poly_eq=0, arg_a=0, idx_b=0, idx_r=0, value_a_f=0, aux=0
        vec![F::ZERO; self.n_columns_f_total()]
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
        aux_1: usize, // op_type: 0=ADD, 1=MUL, 2=POLY_EQ
        aux_2: usize, // is_be: 0=EE, 1=BE
        ctx: &mut InstructionContext<'_>,
    ) -> Result<(), RunnerError> {
        assert!(aux_2 == 0 || aux_2 == 1);
        let trace = ctx.traces.get_mut(&self.table()).unwrap();
        match (aux_1, aux_2) {
            (0, 1) => exec_add_be(arg_a, arg_b, arg_c, ctx.memory, trace),
            (0, 0) => exec_add_ee(arg_a, arg_b, arg_c, ctx.memory, trace),
            (1, 1) => exec_mul_be(arg_a, arg_b, arg_c, ctx.memory, trace),
            (1, 0) => exec_mul_ee(arg_a, arg_b, arg_c, ctx.memory, trace),
            (2, 1) => exec_poly_eq_be(arg_a, arg_b, arg_c, ctx.memory, trace),
            (2, 0) => exec_poly_eq_ee(arg_a, arg_b, arg_c, ctx.memory, trace),
            _ => unreachable!("Invalid extension_op aux_1={aux_1}, aux_2={aux_2}"),
        }
    }
}
