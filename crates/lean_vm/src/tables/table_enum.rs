use backend::*;

use crate::*;

pub const N_TABLES: usize = 3;
pub const ALL_TABLES: [Table; N_TABLES] = [Table::execution(), Table::extension_op(), Table::poseidon16()];
pub const MAX_PRECOMPILE_BUS_WIDTH: usize = 4;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(usize)]
pub enum Table {
    Execution(ExecutionTable<true>),
    ExtensionOp(ExtensionOpPrecompile<true>),
    Poseidon16(Poseidon16Precompile<true>),
}

#[macro_export]
macro_rules! delegate_to_inner {
    // Existing pattern for method calls
    ($self:expr, $method:ident $(, $($arg:expr),*)?) => {
        match $self {
            Self::ExtensionOp(p) => p.$method($($($arg),*)?),
            Self::Poseidon16(p) => p.$method($($($arg),*)?),
            Self::Execution(p) => p.$method($($($arg),*)?),
        }
    };
    // New pattern for applying a macro to the inner value
    ($self:expr => $macro_name:ident) => {
        match $self {
            Table::ExtensionOp(p) => $macro_name!(p),
            Table::Poseidon16(p) => $macro_name!(p),
            Table::Execution(p) => $macro_name!(p),
        }
    };
}

impl Table {
    pub const fn execution() -> Self {
        Self::Execution(ExecutionTable)
    }
    pub const fn extension_op() -> Self {
        Self::ExtensionOp(ExtensionOpPrecompile)
    }
    pub const fn poseidon16() -> Self {
        Self::Poseidon16(Poseidon16Precompile)
    }
    pub fn embed<PF: PrimeCharacteristicRing>(&self) -> PF {
        PF::from_usize(self.index())
    }
    pub const fn index(&self) -> usize {
        unsafe { *(self as *const Self as *const usize) }
    }
}

impl TableT for Table {
    fn name(&self) -> &'static str {
        delegate_to_inner!(self, name)
    }
    fn table(&self) -> Table {
        delegate_to_inner!(self, table)
    }
    fn lookups(&self) -> Vec<LookupIntoMemory> {
        delegate_to_inner!(self, lookups)
    }
    fn is_execution_table(&self) -> bool {
        delegate_to_inner!(self, is_execution_table)
    }
    fn bus(&self) -> Bus {
        delegate_to_inner!(self, bus)
    }
    fn padding_row(&self) -> Vec<PF<EF>> {
        delegate_to_inner!(self, padding_row)
    }
    fn execute(
        &self,
        arg_a: F,
        arg_b: F,
        arg_c: F,
        aux_1: usize,
        aux_2: usize,
        ctx: &mut InstructionContext<'_>,
    ) -> Result<(), RunnerError> {
        delegate_to_inner!(self, execute, arg_a, arg_b, arg_c, aux_1, aux_2, ctx)
    }
    fn n_columns_total(&self) -> usize {
        delegate_to_inner!(self, n_columns_total)
    }
}

impl Air for Table {
    type ExtraData = ();
    fn degree_air(&self) -> usize {
        delegate_to_inner!(self, degree_air)
    }
    fn n_columns(&self) -> usize {
        delegate_to_inner!(self, n_columns)
    }
    fn n_constraints(&self) -> usize {
        delegate_to_inner!(self, n_constraints)
    }
    fn down_column_indexes(&self) -> Vec<usize> {
        delegate_to_inner!(self, down_column_indexes)
    }
    fn eval<AB: AirBuilder>(&self, _: &mut AB, _: &Self::ExtraData) {
        unreachable!()
    }
}

pub fn max_bus_width_including_domainsep() -> usize {
    1 + MAX_PRECOMPILE_BUS_WIDTH.max(N_INSTRUCTION_COLUMNS) // "+1" for domain separation in logup between memory / bytecode / precompiles interactions
}

pub fn max_air_constraints() -> usize {
    ALL_TABLES.iter().map(|table| table.n_constraints()).max().unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_table_indices() {
        for (i, table) in ALL_TABLES.iter().enumerate() {
            assert_eq!(table.index(), i);
        }
    }

    #[test]
    fn test_max_precompile_bus_width() {
        let expected_max_bus_width = ALL_TABLES.iter().map(|table| table.bus().data.len()).max().unwrap();
        assert_eq!(MAX_PRECOMPILE_BUS_WIDTH, expected_max_bus_width);
    }
}
