use crate::{execution::memory::MemoryAccess, *};
use backend::*;

mod air;
use air::*;
mod exec;
pub use exec::fill_trace_memcopy4;

/// Supported source strides. Index 0 ↔ stride_in_flag=1, index 1 ↔ stride_in_flag=0.
pub const MEMCOPY4_STRIDES: [usize; 2] = [0, 4];
/// Hardcoded destination stride.
pub const MEMCOPY4_STRIDE_OUT: usize = 12;

/// Domain separator for memcopy4 in PRECOMPILE_DATA.
pub const MEMCOPY4_DOMAIN_SEP: usize = 5;
/// Multiplier for len in PRECOMPILE_DATA: `aux = DOMAIN_SEP + stride_in_flag + LEN_MULT * len`.
pub const MEMCOPY4_LEN_MULT: usize = 2;

pub const MEMCOPY4_MAX_LEN: usize = 2048;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Memcopy4Precompile<const BUS: bool>;

impl<const BUS: bool> TableT for Memcopy4Precompile<BUS> {
    fn name(&self) -> &'static str {
        "memcopy_4"
    }

    fn table(&self) -> Table {
        Table::memcopy_4()
    }

    fn lookups(&self) -> Vec<LookupIntoMemory> {
        // Single lookup at addr_in validates data = memory[addr_in].
        // addr_out correctness is ensured by exec writing memory[addr_out] = data,
        // verified when the program later reads addr_out via execution table lookups.
        vec![LookupIntoMemory {
            index: COL_ADDR_IN,
            values: (COL_DATA..COL_DATA + 4).collect(),
        }]
    }

    fn bus(&self) -> Bus {
        Bus {
            direction: BusDirection::Pull,
            selector: COL_MC4_ACTIVATION,
            data: vec![
                BusData::Column(COL_MC4_AUX),
                BusData::Column(COL_ADDR_IN),
                BusData::Column(COL_ADDR_OUT),
                BusData::Column(COL_ADDR_IN), // arg_c mirrors addr_in
            ],
        }
    }

    fn n_columns_total(&self) -> usize {
        self.n_columns() + 1 // +1 for COL_MC4_AUX (activation_flag is now an AIR column)
    }

    fn padding_row(&self) -> Vec<F> {
        let mut row = vec![F::ZERO; self.n_columns_total()];
        // activation_flag = 0 on padding (bus inactive)
        row[COL_START] = F::ONE;
        row[COL_LEN] = F::ONE;
        row[COL_MC4_AUX] = F::from_usize(MEMCOPY4_DOMAIN_SEP + MEMCOPY4_LEN_MULT);
        row
    }

    #[inline(always)]
    fn execute<M: MemoryAccess>(
        &self,
        arg_a: F,
        arg_b: F,
        _arg_c: F,
        aux_1: usize, // n_reps
        aux_2: usize, // stride_in_flag (0 or 1)
        ctx: &mut InstructionContext<'_, M>,
    ) -> Result<(), RunnerError> {
        let trace = ctx.traces.get_mut(&self.table()).unwrap();
        exec::exec_memcopy4(arg_a, arg_b, aux_2, aux_1, ctx.memory, trace)
    }
}
