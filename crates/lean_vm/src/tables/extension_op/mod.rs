use crate::{
    tables::extension_op::exec::{
        exec_add_be, exec_add_ee, exec_dot_product_be, exec_dot_product_ee, exec_poly_eq_be, exec_poly_eq_ee,
    },
    *,
};
use backend::*;

mod air;
use air::*;
mod exec;
pub use exec::fill_trace_extension_op;

// domain separation: Poseidon16=1, Poseidon24= 2 or 3 or 4, ExtensionOp>=8
/// Extension op PRECOMPILE_DATA bit-field encoding:
/// aux = 4*is_be + 8*flag_add + 16*flag_mul + 32*flag_poly_eq + 64*len

pub(crate) const EXT_OP_FLAG_IS_BE: usize = 4;
pub(crate) const EXT_OP_FLAG_ADD: usize = 8;
pub(crate) const EXT_OP_FLAG_MUL: usize = 16;
pub(crate) const EXT_OP_FLAG_POLY_EQ: usize = 32;

pub const EXT_OP_ADD_EE: usize = EXT_OP_FLAG_ADD; //       8 + 0 = 8
pub const EXT_OP_ADD_BE: usize = EXT_OP_FLAG_IS_BE + EXT_OP_FLAG_ADD; //       8 + 4 = 12
pub const EXT_OP_DOT_PRODUCT_EE: usize = EXT_OP_FLAG_MUL; //           16 + 0 = 16
pub const EXT_OP_DOT_PRODUCT_BE: usize = EXT_OP_FLAG_IS_BE + EXT_OP_FLAG_MUL; //      16 + 4 = 20
pub const EXT_OP_POLY_EQ_EE: usize = EXT_OP_FLAG_POLY_EQ; //          32 + 0 = 32
pub const EXT_OP_POLY_EQ_BE: usize = EXT_OP_FLAG_IS_BE + EXT_OP_FLAG_POLY_EQ; //  32 + 4 = 36
pub const EXT_OP_LEN_MULTIPLIER: usize = 64;

/// Mapping from zkDSL function names to extension op mode values.
pub const EXT_OP_FUNCTIONS: [(&str, usize); 6] = [
    ("add_ee", EXT_OP_ADD_EE),
    ("add_be", EXT_OP_ADD_BE),
    ("dot_product_ee", EXT_OP_DOT_PRODUCT_EE),
    ("dot_product_be", EXT_OP_DOT_PRODUCT_BE),
    ("poly_eq_ee", EXT_OP_POLY_EQ_EE),
    ("poly_eq_be", EXT_OP_POLY_EQ_BE),
];

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExtensionOpPrecompile<const BUS: bool>;

impl<const BUS: bool> TableT for ExtensionOpPrecompile<BUS> {
    fn name(&self) -> &'static str {
        "extension_op"
    }

    fn table(&self) -> Table {
        Table::extension_op()
    }

    fn lookups(&self) -> Vec<LookupIntoMemory> {
        vec![
            LookupIntoMemory {
                index: COL_IDX_A,
                values: (COL_VA..COL_VA + DIMENSION).collect(),
            },
            LookupIntoMemory {
                index: COL_IDX_B,
                values: (COL_VB..COL_VB + DIMENSION).collect(),
            },
            LookupIntoMemory {
                index: COL_IDX_RES,
                values: (COL_VRES..COL_VRES + DIMENSION).collect(),
            },
        ]
    }

    fn bus(&self) -> Bus {
        Bus {
            direction: BusDirection::Pull,
            selector: COL_ACTIVATION_FLAG,
            data: vec![
                BusData::Column(COL_AUX_EXTENSION_OP),
                BusData::Column(COL_IDX_A),
                BusData::Column(COL_IDX_B),
                BusData::Column(COL_IDX_RES),
            ],
        }
    }

    fn n_columns_total(&self) -> usize {
        self.n_columns() + 2 // +2 for COL_ACTIVATION_FLAG and COL_AUX_EXTENSION_OP (non-AIR, used in bus logup)
    }

    fn padding_row(&self) -> Vec<F> {
        let mut row = vec![F::ZERO; self.n_columns_total()];
        row[COL_START] = F::ONE;
        row[COL_LEN] = F::ONE;
        row[COL_AUX_EXTENSION_OP] = F::from_usize(EXT_OP_LEN_MULTIPLIER);
        row
    }

    #[inline(always)]
    fn execute(
        &self,
        arg_a: F,
        arg_b: F,
        arg_c: F,
        aux_1: usize, // size (length N)
        aux_2: usize, // mode: is_be + 2*flag_mul + 4*flag_poly_eq
        ctx: &mut InstructionContext<'_>,
    ) -> Result<(), RunnerError> {
        let trace = ctx.traces.get_mut(&self.table()).unwrap();
        match aux_2 {
            EXT_OP_ADD_EE => exec_add_ee(arg_a, arg_b, arg_c, aux_1, ctx.memory, trace),
            EXT_OP_ADD_BE => exec_add_be(arg_a, arg_b, arg_c, aux_1, ctx.memory, trace),
            EXT_OP_DOT_PRODUCT_EE => exec_dot_product_ee(arg_a, arg_b, arg_c, aux_1, ctx.memory, trace),
            EXT_OP_DOT_PRODUCT_BE => exec_dot_product_be(arg_a, arg_b, arg_c, aux_1, ctx.memory, trace),
            EXT_OP_POLY_EQ_EE => exec_poly_eq_ee(arg_a, arg_b, arg_c, aux_1, ctx.memory, trace),
            EXT_OP_POLY_EQ_BE => exec_poly_eq_be(arg_a, arg_b, arg_c, aux_1, ctx.memory, trace),
            _ => unreachable!("Invalid extension_op mode={aux_2}"),
        }
    }
}
