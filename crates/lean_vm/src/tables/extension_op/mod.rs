use crate::{
    execution::memory::MemoryAccess,
    tables::extension_op::exec::{exec_memcopy_4, exec_multi_row},
    *,
};
use backend::*;

mod air;
use air::*;
mod exec;
pub use exec::fill_trace_extension_op;

// domain separation: Poseidon16=1, Poseidon24= 2 or 3 or 4, ExtensionOp>=8
/// Extension op PRECOMPILE_DATA bit-field encoding:
/// aux = 4*is_be + 8*flag_add + 16*flag_mul + 32*flag_poly_eq + 64*flag_memcopy_4
///     + 128*len
///
/// The is_be bit (bit 2) selects BE vs EE for add/mul/poly_eq,
/// or `MEMCOPY4_STRIDES[1]` vs `MEMCOPY4_STRIDES[0]` for memcopy_4.
pub const EXT_OP_FLAG_IS_BE: usize = 4;
pub(crate) const EXT_OP_FLAG_ADD: usize = 8;
pub(crate) const EXT_OP_FLAG_MUL: usize = 16;
pub(crate) const EXT_OP_FLAG_POLY_EQ: usize = 32;
pub const EXT_OP_FLAG_MEMCOPY_4: usize = 64;

pub const EXT_OP_LEN_MULTIPLIER: usize = 128;
/// Maximum supported `size` / `n_reps` value (exclusive upper bound).
pub const MAX_EXT_OP_LEN: usize = 2048;

/// Supported source strides for memcopy_4. Index 0 ↔ is_be bit off, index 1 ↔ is_be bit on.
pub const MEMCOPY4_STRIDES: [usize; 2] = [0, 4];
/// Hardcoded destination stride for memcopy_4 mode.
pub const MEMCOPY_4_STRIDE_OUT: usize = 8;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ExtensionOp {
    Add,
    Mul,
    PolyEq,
}

impl ExtensionOp {
    fn from_name(name: &str) -> Option<Self> {
        match name {
            "add" => Some(Self::Add),
            "dot_product" => Some(Self::Mul),
            "poly_eq" => Some(Self::PolyEq),
            _ => None,
        }
    }

    pub(crate) const fn flag(self) -> usize {
        match self {
            Self::Add => EXT_OP_FLAG_ADD,
            Self::Mul => EXT_OP_FLAG_MUL,
            Self::PolyEq => EXT_OP_FLAG_POLY_EQ,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExtensionOpMode {
    pub op: ExtensionOp,
    pub is_be: bool,
}

impl ExtensionOpMode {
    pub fn from_name(name: &str) -> Option<Self> {
        let (prefix, suffix) = name.rsplit_once('_')?;
        let is_be = match suffix {
            "ee" => false,
            "be" => true,
            _ => return None,
        };
        Some(Self {
            op: ExtensionOp::from_name(prefix)?,
            is_be,
        })
    }

    pub const fn flag_encoding(self) -> usize {
        self.op.flag() + self.is_be as usize * EXT_OP_FLAG_IS_BE
    }

    pub const fn name(self) -> &'static str {
        match (self.op, self.is_be) {
            (ExtensionOp::Add, false) => "add_ee",
            (ExtensionOp::Add, true) => "add_be",
            (ExtensionOp::Mul, false) => "dot_product_ee",
            (ExtensionOp::Mul, true) => "dot_product_be",
            (ExtensionOp::PolyEq, false) => "poly_eq_ee",
            (ExtensionOp::PolyEq, true) => "poly_eq_be",
        }
    }
}

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
        args: PrecompileCompTimeArgs<usize>,
        ctx: &mut InstructionContext<'_, M>,
    ) -> Result<(), RunnerError> {
        let trace = ctx.traces.get_mut(&self.table()).unwrap();
        match args {
            PrecompileCompTimeArgs::ExtensionOp { size, mode } => {
                exec_multi_row(arg_a, arg_b, arg_c, size, mode.is_be, mode.op, ctx.memory, trace)
            }
            PrecompileCompTimeArgs::Memcopy4 { n_reps, stride_in } => {
                exec_memcopy_4(arg_a, arg_b, stride_in, n_reps, ctx.memory, trace)
            }
            _ => unreachable!("ExtensionOp table called with non-ExtensionOp args"),
        }
    }
}
