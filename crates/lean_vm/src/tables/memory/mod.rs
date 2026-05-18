use crate::execution::memory::MemoryAccess;
use crate::*;
use backend::*;

/// Memory "table": 2 committed columns (value, multiplicity).
/// Has no AIR constraints and no bus of its own — memory's pull-side
/// participation in the Logup/GKR instance is hardcoded as a special case
/// (implicit row-as-index). Other tables push `(value, index)` tuples to
/// memory via the existing `LookupIntoMemory` mechanism.
pub const MEMORY_COL_VALUE: ColIndex = 0;
pub const MEMORY_COL_ACC: ColIndex = 1;
pub const MEMORY_N_COLUMNS: usize = 2;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MemoryTable;

impl TableT for MemoryTable {
    fn name(&self) -> &'static str {
        "memory"
    }

    fn table(&self) -> Table {
        Table::memory()
    }

    fn lookups(&self) -> Vec<LookupIntoMemory> {
        vec![]
    }

    fn bus(&self) -> Bus {
        // Memory's contribution to Logup is hardcoded (implicit index) — not a normal bus.
        unreachable!("MemoryTable::bus should not be called; memory is special-cased in logup")
    }

    fn padding_row(&self, _zero_vec_ptr: usize, _null_hash_ptr: usize, _ending_pc: usize) -> Vec<F> {
        vec![F::ZERO; MEMORY_N_COLUMNS]
    }

    fn execute<M: MemoryAccess>(
        &self,
        _arg_a: F,
        _arg_b: F,
        _arg_c: F,
        _args: PrecompileCompTimeArgs<usize>,
        _ctx: &mut InstructionContext<'_, M>,
    ) -> Result<(), RunnerError> {
        unreachable!("MemoryTable::execute should not be called; memory is not an executable precompile")
    }
}

impl Air for MemoryTable {
    type ExtraData = ExtraDataForBuses<EF>;

    fn n_columns(&self) -> usize {
        MEMORY_N_COLUMNS
    }

    fn degree_air(&self) -> usize {
        1
    }

    fn n_constraints(&self) -> usize {
        0
    }

    fn n_shift_columns(&self) -> usize {
        0
    }

    fn eval<AB: AirBuilder>(&self, _builder: &mut AB, _extra_data: &Self::ExtraData) {
        // No constraints — memory has no AIR.
    }
}
