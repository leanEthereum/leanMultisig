use crate::{
    tables::{EXTENSION_PRECOMPILE_ENCODING_BIT_SIZE, extension_op::exec::exec_multi_row},
    *,
};
use backend::*;

mod air;
use air::*;
mod exec;
pub use exec::fill_trace_extension_op;

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
        row[COL_AUX_EXTENSION_OP] = F::from_usize(1 << EXTENSION_PRECOMPILE_ENCODING_BIT_SIZE);
        row
    }

    #[inline(always)]
    fn execute(
        &self,
        arg_a: F,
        arg_b: F,
        arg_c: F,
        aux_arg: &PrecompileAuxArg,
        ctx: &mut InstructionContext<'_>,
    ) -> Result<(), RunnerError> {
        let trace = ctx.traces.get_mut(&self.table()).unwrap();
        let aux_arg = match aux_arg {
            PrecompileAuxArg::Extension(mode) => mode,
            _ => unreachable!(),
        };
        exec_multi_row(arg_a, arg_b, arg_c, aux_arg, ctx.memory, trace)
    }
}
