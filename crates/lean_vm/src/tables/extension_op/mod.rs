use crate::{
    execution::memory::MemoryAccess,
    tables::extension_op::exec::{
        exec_add_be, exec_add_ee, exec_dot_product_be, exec_dot_product_ee, exec_memcopy_4, exec_poly_eq_be,
        exec_poly_eq_ee,
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
/// aux = 4*variant + 8*flag_add + 16*flag_mul + 32*flag_poly_eq + 64*flag_memcopy_4
///     + 128*len
///
/// The variant bit (bit 2) selects BE vs EE for add/mul/poly_eq,
/// or `MEMCOPY4_STRIDES[1]` vs `MEMCOPY4_STRIDES[0]` for memcopy_4.
pub const EXT_OP_FLAG_VARIANT: usize = 4;
pub(crate) const EXT_OP_FLAG_ADD: usize = 8;
pub(crate) const EXT_OP_FLAG_MUL: usize = 16;
pub(crate) const EXT_OP_FLAG_POLY_EQ: usize = 32;
pub const EXT_OP_FLAG_MEMCOPY_4: usize = 64;

pub const EXT_OP_ADD_EE: usize = EXT_OP_FLAG_ADD;
pub const EXT_OP_ADD_BE: usize = EXT_OP_FLAG_VARIANT + EXT_OP_FLAG_ADD;
pub const EXT_OP_DOT_PRODUCT_EE: usize = EXT_OP_FLAG_MUL;
pub const EXT_OP_DOT_PRODUCT_BE: usize = EXT_OP_FLAG_VARIANT + EXT_OP_FLAG_MUL;
pub const EXT_OP_POLY_EQ_EE: usize = EXT_OP_FLAG_POLY_EQ;
pub const EXT_OP_POLY_EQ_BE: usize = EXT_OP_FLAG_VARIANT + EXT_OP_FLAG_POLY_EQ;
/// memcopy_4 with variant=0 → stride_in = MEMCOPY4_STRIDES[0].
pub const EXT_OP_MEMCOPY_4_V0: usize = EXT_OP_FLAG_MEMCOPY_4;
/// memcopy_4 with variant=1 → stride_in = MEMCOPY4_STRIDES[1].
pub const EXT_OP_MEMCOPY_4_V1: usize = EXT_OP_FLAG_MEMCOPY_4 + EXT_OP_FLAG_VARIANT;

/// Supported source strides for memcopy_4. Index 0 ↔ variant bit off, index 1 ↔ variant bit on.
pub const MEMCOPY4_STRIDES: [usize; 2] = [0, 4];
/// Hardcoded destination stride for memcopy_4 mode.
pub const MEMCOPY_4_STRIDE_OUT: usize = 8;

pub const EXT_OP_LEN_MULTIPLIER: usize = 128;
/// Maximum supported `size` / `n_reps` value (exclusive upper bound).
pub const MAX_EXT_OP_LEN: usize = 2048;

/// Mapping from zkDSL function names to extension op mode values.
pub const EXT_OP_FUNCTIONS: [(&str, usize); 8] = [
    ("add_ee", EXT_OP_ADD_EE),
    ("add_be", EXT_OP_ADD_BE),
    ("dot_product_ee", EXT_OP_DOT_PRODUCT_EE),
    ("dot_product_be", EXT_OP_DOT_PRODUCT_BE),
    ("poly_eq_ee", EXT_OP_POLY_EQ_EE),
    ("poly_eq_be", EXT_OP_POLY_EQ_BE),
    ("memcopy_4", EXT_OP_MEMCOPY_4_V0),
    ("memcopy_4", EXT_OP_MEMCOPY_4_V1),
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
    fn execute<M: MemoryAccess>(
        &self,
        arg_a: F,
        arg_b: F,
        arg_c: F,
        aux_1: usize,
        aux_2: usize,
        ctx: &mut InstructionContext<'_, M>,
    ) -> Result<(), RunnerError> {
        let trace = ctx.traces.get_mut(&self.table()).unwrap();
        let flag_bits = aux_2 & (EXT_OP_LEN_MULTIPLIER - 1);
        match flag_bits {
            EXT_OP_ADD_EE => exec_add_ee(arg_a, arg_b, arg_c, aux_1, ctx.memory, trace),
            EXT_OP_ADD_BE => exec_add_be(arg_a, arg_b, arg_c, aux_1, ctx.memory, trace),
            EXT_OP_DOT_PRODUCT_EE => exec_dot_product_ee(arg_a, arg_b, arg_c, aux_1, ctx.memory, trace),
            EXT_OP_DOT_PRODUCT_BE => exec_dot_product_be(arg_a, arg_b, arg_c, aux_1, ctx.memory, trace),
            EXT_OP_POLY_EQ_EE => exec_poly_eq_ee(arg_a, arg_b, arg_c, aux_1, ctx.memory, trace),
            EXT_OP_POLY_EQ_BE => exec_poly_eq_be(arg_a, arg_b, arg_c, aux_1, ctx.memory, trace),
            EXT_OP_MEMCOPY_4_V0 | EXT_OP_MEMCOPY_4_V1 => {
                let variant = ((flag_bits & EXT_OP_FLAG_VARIANT) != 0) as usize;
                exec_memcopy_4(arg_a, arg_b, MEMCOPY4_STRIDES[variant], aux_1, ctx.memory, trace)
            }
            _ => unreachable!("Invalid extension_op mode={aux_2}"),
        }
    }
}
