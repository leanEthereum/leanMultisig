use multilinear_toolkit::prelude::PrimeCharacteristicRing;
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
            Self::Execution(_) => TABLE_EXECUTION,
            Self::DotProduct(_) => TABLE_DOT_PRODUCT,
            Self::Poseidon16(_) => TABLE_POSEIDON_16,
            Self::Poseidon24(_) => TABLE_POSEIDON_24,
            Self::MultilinearEval(_) => TABLE_MULTILINEAR_EVAL,
        }
    }
    pub fn from_index(index: usize) -> Self {
        match index {
            TABLE_DOT_PRODUCT => Self::dot_product(),
            TABLE_POSEIDON_16 => Self::poseidon16(),
            TABLE_POSEIDON_24 => Self::poseidon24(),
            TABLE_MULTILINEAR_EVAL => Self::multilinear_eval(),
            _ => panic!("Invalid table index: {}", index),
        }
    }
}

impl TableT for Table {
    fn name(&self) -> &'static str {
        match self {
            Self::DotProduct(p) => p.name(),
            Self::Poseidon16(p) => p.name(),
            Self::Poseidon24(p) => p.name(),
            Self::MultilinearEval(p) => p.name(),
            Self::Execution(p) => p.name(),
        }
    }
    fn identifier(&self) -> Table {
        match self {
            Self::DotProduct(p) => p.identifier(),
            Self::Poseidon16(p) => p.identifier(),
            Self::Poseidon24(p) => p.identifier(),
            Self::MultilinearEval(p) => p.identifier(),
            Self::Execution(p) => p.identifier(),
        }
    }
    fn commited_columns_f(&self) -> Vec<ColIndex> {
        match self {
            Self::DotProduct(p) => p.commited_columns_f(),
            Self::Poseidon16(p) => p.commited_columns_f(),
            Self::Poseidon24(p) => p.commited_columns_f(),
            Self::MultilinearEval(p) => p.commited_columns_f(),
            Self::Execution(p) => p.commited_columns_f(),
        }
    }
    fn commited_columns_ef(&self) -> Vec<ColIndex> {
        match self {
            Self::DotProduct(p) => p.commited_columns_ef(),
            Self::Poseidon16(p) => p.commited_columns_ef(),
            Self::Poseidon24(p) => p.commited_columns_ef(),
            Self::MultilinearEval(p) => p.commited_columns_ef(),
            Self::Execution(p) => p.commited_columns_ef(),
        }
    }
    fn normal_lookups_f(&self) -> Vec<LookupIntoMemory> {
        match self {
            Self::DotProduct(p) => p.normal_lookups_f(),
            Self::Poseidon16(p) => p.normal_lookups_f(),
            Self::Poseidon24(p) => p.normal_lookups_f(),
            Self::MultilinearEval(p) => p.normal_lookups_f(),
            Self::Execution(p) => p.normal_lookups_f(),
        }
    }
    fn normal_lookups_ef(&self) -> Vec<ExtensionFieldLookupIntoMemory> {
        match self {
            Self::DotProduct(p) => p.normal_lookups_ef(),
            Self::Poseidon16(p) => p.normal_lookups_ef(),
            Self::Poseidon24(p) => p.normal_lookups_ef(),
            Self::MultilinearEval(p) => p.normal_lookups_ef(),
            Self::Execution(p) => p.normal_lookups_ef(),
        }
    }
    fn vector_lookups(&self) -> Vec<VectorLookupIntoMemory> {
        match self {
            Self::DotProduct(p) => p.vector_lookups(),
            Self::Poseidon16(p) => p.vector_lookups(),
            Self::Poseidon24(p) => p.vector_lookups(),
            Self::MultilinearEval(p) => p.vector_lookups(),
            Self::Execution(p) => p.vector_lookups(),
        }
    }
    fn buses(&self) -> Vec<Bus> {
        match self {
            Self::DotProduct(p) => p.buses(),
            Self::Poseidon16(p) => p.buses(),
            Self::Poseidon24(p) => p.buses(),
            Self::MultilinearEval(p) => p.buses(),
            Self::Execution(p) => p.buses(),
        }
    }
    fn padding_row(&self) -> Vec<EF> {
        match self {
            Self::DotProduct(p) => p.padding_row(),
            Self::Poseidon16(p) => p.padding_row(),
            Self::Poseidon24(p) => p.padding_row(),
            Self::MultilinearEval(p) => p.padding_row(),
            Self::Execution(p) => p.padding_row(),
        }
    }
    fn execute(
        &self,
        arg_a: F,
        arg_b: F,
        arg_c: F,
        aux: usize,
        ctx: &mut InstructionContext<'_>,
    ) -> Result<(), RunnerError> {
        match self {
            Self::DotProduct(p) => p.execute(arg_a, arg_b, arg_c, aux, ctx),
            Self::Poseidon16(p) => p.execute(arg_a, arg_b, arg_c, aux, ctx),
            Self::Poseidon24(p) => p.execute(arg_a, arg_b, arg_c, aux, ctx),
            Self::MultilinearEval(p) => p.execute(arg_a, arg_b, arg_c, aux, ctx),
            Self::Execution(p) => p.execute(arg_a, arg_b, arg_c, aux, ctx),
        }
    }
}

impl Air for Table {
    type ExtraData = ();
    fn degree(&self) -> usize {
        match self {
            Self::DotProduct(p) => p.degree(),
            Self::Poseidon16(p) => p.degree(),
            Self::Poseidon24(p) => p.degree(),
            Self::MultilinearEval(p) => p.degree(),
            Self::Execution(p) => p.degree(),
        }
    }
    fn n_columns_f(&self) -> usize {
        match self {
            Self::DotProduct(p) => p.n_columns_f(),
            Self::Poseidon16(p) => p.n_columns_f(),
            Self::Poseidon24(p) => p.n_columns_f(),
            Self::MultilinearEval(p) => p.n_columns_f(),
            Self::Execution(p) => p.n_columns_f(),
        }
    }
    fn n_columns_ef(&self) -> usize {
        match self {
            Self::DotProduct(p) => p.n_columns_ef(),
            Self::Poseidon16(p) => p.n_columns_ef(),
            Self::Poseidon24(p) => p.n_columns_ef(),
            Self::MultilinearEval(p) => p.n_columns_ef(),
            Self::Execution(p) => p.n_columns_ef(),
        }
    }
    fn n_constraints(&self) -> usize {
        match self {
            Self::DotProduct(p) => p.n_constraints(),
            Self::Poseidon16(p) => p.n_constraints(),
            Self::Poseidon24(p) => p.n_constraints(),
            Self::MultilinearEval(p) => p.n_constraints(),
            Self::Execution(p) => p.n_constraints(),
        }
    }
    fn down_column_indexes(&self) -> Vec<usize> {
        match self {
            Self::DotProduct(p) => p.down_column_indexes(),
            Self::Poseidon16(p) => p.down_column_indexes(),
            Self::Poseidon24(p) => p.down_column_indexes(),
            Self::MultilinearEval(p) => p.down_column_indexes(),
            Self::Execution(p) => p.down_column_indexes(),
        }
    }
    fn eval<AB: p3_air::AirBuilder>(&self, _: &mut AB, _: &Self::ExtraData) {
        unreachable!()
    }
}
