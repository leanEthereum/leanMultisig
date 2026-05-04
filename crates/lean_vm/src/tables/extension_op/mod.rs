use crate::{execution::memory::MemoryAccess, tables::extension_op::exec::exec_multi_row, *};
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
pub const EXT_OP_LEN_MULTIPLIER: usize = 64;

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

    #[allow(clippy::vec_init_then_push)] // https://github.com/leanEthereum/leanMultisig/issues/198
    fn bus(&self) -> Bus {
        let mut data = Vec::with_capacity(4);
        data.push(BusData::Column(COL_AUX_EXTENSION_OP));
        data.push(BusData::Column(COL_IDX_A));
        data.push(BusData::Column(COL_IDX_B));
        data.push(BusData::Column(COL_IDX_RES));
        Bus {
            direction: BusDirection::Pull,
            selector: COL_ACTIVATION_FLAG,
            data,
        }
    }

    fn n_columns_total(&self) -> usize {
        self.n_columns() + 2 // +2 for COL_ACTIVATION_FLAG and COL_AUX_EXTENSION_OP (non-AIR, used in bus logup)
    }

    fn padding_row(&self, padding: &PaddingMemory) -> Vec<F> {
        let mut row = vec![F::ZERO; self.n_columns_total()];
        row[COL_START] = F::ONE;
        row[COL_LEN] = F::ONE;
        row[COL_AUX_EXTENSION_OP] = F::from_usize(EXT_OP_LEN_MULTIPLIER);
        row[COL_IDX_A] = F::from_usize(padding.zero_vec_ptr);
        row[COL_IDX_B] = F::from_usize(padding.zero_vec_ptr);
        row[COL_IDX_RES] = F::from_usize(padding.zero_vec_ptr);
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
        let PrecompileCompTimeArgs::ExtensionOp { size, mode } = args else {
            unreachable!("ExtensionOp table called with non-ExtensionOp args");
        };
        let trace = ctx.traces.get_mut(&self.table()).unwrap();
        exec_multi_row(arg_a, arg_b, arg_c, size, mode.is_be, mode.op, ctx.memory, trace)
    }
}
