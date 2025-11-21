use multilinear_toolkit::prelude::{PF, PrimeCharacteristicRing};
use p3_air::Air;

use crate::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Table {
    Execution(ExecutionTable),
    DotProduct(DotProductPrecompile),
    Poseidon16(Poseidon16Precompile),
    Poseidon24(Poseidon24Precompile),
    MultilinearEval(MultilinearEvalPrecompile),
}

pub const TABLE_DOT_PRODUCT: usize = 0;
pub const TABLE_POSEIDON_16: usize = 1;
pub const TABLE_POSEIDON_24: usize = 2;
pub const TABLE_MULTILINEAR_EVAL: usize = 3;
pub const TABLE_EXECUTION: usize = 1000;

macro_rules! delegate_to_inner {
    ($self:expr, $method:ident $(, $($arg:expr),*)?) => {
        match $self {
            Self::DotProduct(p) => p.$method($($($arg),*)?),
            Self::Poseidon16(p) => p.$method($($($arg),*)?),
            Self::Poseidon24(p) => p.$method($($($arg),*)?),
            Self::MultilinearEval(p) => p.$method($($($arg),*)?),
            Self::Execution(p) => p.$method($($($arg),*)?),
        }
    };
}

impl Table {
    pub const fn dot_product() -> Self {
        Self::DotProduct(DotProductPrecompile)
    }
    pub const fn poseidon16() -> Self {
        Self::Poseidon16(Poseidon16Precompile)
    }
    pub const fn poseidon24() -> Self {
        Self::Poseidon24(Poseidon24Precompile)
    }
    pub const fn multilinear_eval() -> Self {
        Self::MultilinearEval(MultilinearEvalPrecompile)
    }
    pub const fn execution() -> Self {
        Self::Execution(ExecutionTable)
    }
    pub fn embed<PF: PrimeCharacteristicRing>(&self) -> PF {
        PF::from_usize(self.index())
    }
    pub fn index(&self) -> usize {
        match self {
            Self::DotProduct(_) => TABLE_DOT_PRODUCT,
            Self::Poseidon16(_) => TABLE_POSEIDON_16,
            Self::Poseidon24(_) => TABLE_POSEIDON_24,
            Self::MultilinearEval(_) => TABLE_MULTILINEAR_EVAL,
            Self::Execution(_) => TABLE_EXECUTION,
        }
    }
    pub fn from_index(index: usize) -> Self {
        match index {
            TABLE_DOT_PRODUCT => Self::dot_product(),
            TABLE_POSEIDON_16 => Self::poseidon16(),
            TABLE_POSEIDON_24 => Self::poseidon24(),
            TABLE_MULTILINEAR_EVAL => Self::multilinear_eval(),
            TABLE_EXECUTION => Self::execution(),
            _ => panic!("Invalid table index: {}", index),
        }
    }
}

impl TableT for Table {
    fn name(&self) -> &'static str {
        delegate_to_inner!(self, name)
    }
    fn identifier(&self) -> Table {
        delegate_to_inner!(self, identifier)
    }
    fn commited_columns_f(&self) -> Vec<ColIndex> {
        delegate_to_inner!(self, commited_columns_f)
    }
    fn commited_columns_ef(&self) -> Vec<ColIndex> {
        delegate_to_inner!(self, commited_columns_ef)
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
    fn degree(&self) -> usize {
        delegate_to_inner!(self, degree)
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
    fn eval<AB: p3_air::AirBuilder>(&self, _: &mut AB, _: &Self::ExtraData) {
        unreachable!()
    }
}