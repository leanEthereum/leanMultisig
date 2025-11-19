use crate::{EF, F, Memory, RunnerError, Table};
use p3_air::Air;

mod dot_product;
pub use dot_product::*;

pub type ColIndex = usize;

#[derive(Debug)]
pub struct LookupIntoMemory {
    pub index: ColIndex,
    pub values: ColIndex,
}

#[derive(Debug)]
pub struct ExtensionFieldLookupIntoMemory {
    pub index: ColIndex,
    pub values: ColIndex,
}

#[derive(Debug)]
pub struct VectorLookupIntoMemory {
    pub index: ColIndex,
    pub values: [ColIndex; 8],
}

#[derive(Debug)]
pub enum BusDirection {
    Pull,
    Push,
}

#[derive(Debug)]
pub struct Bus {
    pub direction: BusDirection,
    pub table: Table,
    pub selector: ColIndex,
    pub data: Vec<ColIndex>,
}

#[derive(Debug)]
pub struct PrecompileTrace {
    pub base: Vec<Vec<F>>,
    pub ext: Vec<Vec<EF>>,
    pub padding_len: usize,
}

impl PrecompileTrace {
    pub fn new<A: Air>() -> Self {
        Self {
            base: vec![Vec::new(); A::n_columns_f()],
            ext: vec![Vec::new(); A::n_columns_ef()],
            padding_len: 0,
        }
    }
}

pub trait ModularPrecompile: Air {
    fn name() -> &'static str;
    fn identifier() -> Table;
    fn commited_columns() -> &'static [ColIndex];
    fn simple_lookups() -> &'static [LookupIntoMemory];
    fn ext_field_lookups() -> &'static [ExtensionFieldLookupIntoMemory];
    fn vector_lookups() -> &'static [VectorLookupIntoMemory];
    fn buses() -> &'static [Bus];
    fn execute(
        arg_a: F,
        arg_b: F,
        arg_c: F,
        aux: usize,
        memory: &mut Memory,
        trace: &mut PrecompileTrace,
    ) -> Result<(), RunnerError>;
    fn padding_row() -> Vec<EF>;

    fn air_padding_row() -> Vec<EF> {
        // only the shited_columns
        Self::down_column_indexes()
            .into_iter()
            .map(|i| Self::padding_row()[i])
            .collect()
    }
}
