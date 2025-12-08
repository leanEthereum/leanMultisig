use multilinear_toolkit::prelude::*;

use crate::*;

pub const N_TABLES: usize = 4;
pub const ALL_TABLES: [Table; N_TABLES] = [
    Table::execution(),
    Table::dot_product_be(),
    Table::dot_product_ee(),
    Table::poseidon16(),
];

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(usize)]
pub enum Table {
    Execution(ExecutionTable),
    DotProductBE(DotProductPrecompile<true>),
    DotProductEE(DotProductPrecompile<false>),
    Poseidon16(Poseidon16Precompile<true>),
}

#[macro_export]
macro_rules! delegate_to_inner {
    // Existing pattern for method calls
    ($self:expr, $method:ident $(, $($arg:expr),*)?) => {
        match $self {
            Self::DotProductBE(p) => p.$method($($($arg),*)?),
            Self::DotProductEE(p) => p.$method($($($arg),*)?),
            Self::Poseidon16(p) => p.$method($($($arg),*)?),
            Self::Execution(p) => p.$method($($($arg),*)?),
        }
    };
    // New pattern for applying a macro to the inner value
    ($self:expr => $macro_name:ident) => {
        match $self {
            Table::DotProductBE(p) => $macro_name!(p),
            Table::DotProductEE(p) => $macro_name!(p),
            Table::Poseidon16(p) => $macro_name!(p),
            Table::Execution(p) => $macro_name!(p),
        }
    };
}

impl Table {
    pub const fn execution() -> Self {
        Self::Execution(ExecutionTable)
    }
    pub const fn dot_product_be() -> Self {
        Self::DotProductBE(DotProductPrecompile::<true>)
    }
    pub const fn dot_product_ee() -> Self {
        Self::DotProductEE(DotProductPrecompile::<false>)
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
    fn identifier(&self) -> Table {
        delegate_to_inner!(self, identifier)
    }
    fn normal_lookups_f(&self) -> Vec<LookupIntoMemory> {
        delegate_to_inner!(self, normal_lookups_f)
    }
    fn normal_lookups_ef(&self) -> Vec<ExtensionFieldLookupIntoMemory> {
        delegate_to_inner!(self, normal_lookups_ef)
    }
    fn vector_lookups(&self) -> Vec<VectorLookupIntoMemory> {
        delegate_to_inner!(self, vector_lookups)
    }
    fn buses(&self) -> Vec<Bus> {
        delegate_to_inner!(self, buses)
    }
    fn padding_row_f(&self) -> Vec<PF<EF>> {
        delegate_to_inner!(self, padding_row_f)
    }
    fn padding_row_ef(&self) -> Vec<EF> {
        delegate_to_inner!(self, padding_row_ef)
    }
    fn execute(
        &self,
        arg_a: F,
        arg_b: F,
        arg_c: F,
        aux: usize,
        ctx: &mut InstructionContext<'_>,
    ) -> Result<(), RunnerError> {
        delegate_to_inner!(self, execute, arg_a, arg_b, arg_c, aux, ctx)
    }
    fn n_columns_f_total(&self) -> usize {
        delegate_to_inner!(self, n_columns_f_total)
    }
    fn n_columns_ef_total(&self) -> usize {
        delegate_to_inner!(self, n_columns_ef_total)
    }
}

impl Air for Table {
    type ExtraData = ();
    fn degree_air(&self) -> usize {
        delegate_to_inner!(self, degree_air)
    }
    fn n_columns_f_air(&self) -> usize {
        delegate_to_inner!(self, n_columns_f_air)
    }
    fn n_columns_ef_air(&self) -> usize {
        delegate_to_inner!(self, n_columns_ef_air)
    }
    fn n_constraints(&self) -> usize {
        delegate_to_inner!(self, n_constraints)
    }
    fn down_column_indexes_f(&self) -> Vec<usize> {
        delegate_to_inner!(self, down_column_indexes_f)
    }
    fn down_column_indexes_ef(&self) -> Vec<usize> {
        delegate_to_inner!(self, down_column_indexes_ef)
    }
    fn eval<AB: AirBuilder>(&self, _: &mut AB, _: &Self::ExtraData) {
        unreachable!()
    }
}

pub fn max_bus_width() -> usize {
    1 + ALL_TABLES
        .iter()
        .map(|table| table.buses().iter().map(|bus| bus.data.len()).max().unwrap())
        .max()
        .unwrap()
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
}
