use multilinear_toolkit::prelude::ProofResult;
use p3_air::Air;

use crate::{EF, F, Memory, Table};

pub type ColIndex = usize;
pub type BusIndex = usize;

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
    pub bus_index: BusIndex,
    pub data: Vec<ColIndex>, // only commited columns (for now)
}

#[derive(Debug)]
pub struct PrecompileTrace {
    pub base: Vec<Vec<F>>,
    pub ext: Vec<Vec<EF>>,
}

pub trait ModularPrecompile: Air {
    type Witness: Send + Sync;

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
        aux: F,
        memory: &mut Memory,
    ) -> ProofResult<Self::Witness>;
    fn gen_trace(witness: &[Self::Witness], memory: &[F]) -> ProofResult<PrecompileTrace>;
}
