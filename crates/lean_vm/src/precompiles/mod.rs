use std::{any::TypeId, mem::transmute_copy};

use crate::{EF, F, Memory, RunnerError, Table};
use multilinear_toolkit::prelude::*;
use p3_air::Air;

mod dot_product;
pub use dot_product::*;

mod poseidon_16;
pub use poseidon_16::*;

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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BusSelector {
    Column(ColIndex),
    DenseOnes, // [1, 1, 1, ..., 1, 1, 0, 0, ..., 0] (padding in the end)
}

#[derive(Debug)]
pub struct Bus {
    pub direction: BusDirection,
    pub table: Table,
    pub selector: BusSelector,
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

    pub fn n_rows_non_padded(&self) -> usize {
        self.base[0].len() - self.padding_len
    }

    pub fn n_rows_padded(&self) -> usize {
        assert!(self.base[0].len().is_power_of_two());
        self.base[0].len()
    }
}

#[derive(Debug)]
pub struct ExtraDataForBuses<EF> {
    // GKR quotient challenges
    pub bus_challenge: EF,
    pub fingerprint_challenge_powers: [EF; 5],
    pub bus_beta: EF,
    pub alpha_powers: Vec<EF>,
}

impl AlphaPowersMut<EF> for ExtraDataForBuses<EF> {
    fn alpha_powers_mut(&mut self) -> &mut Vec<EF> {
        &mut self.alpha_powers
    }
}

impl AlphaPowers<EF> for ExtraDataForBuses<EF> {
    fn alpha_powers(&self) -> &[EF] {
        &self.alpha_powers
    }
}

impl<EF: ExtensionField<PF<EF>>> ExtraDataForBuses<EF> {
    pub fn transmute_bus_data<NewEF: 'static>(&self) -> (NewEF, [NewEF; 5], NewEF) {
        if TypeId::of::<NewEF>() == TypeId::of::<EF>() {
            unsafe {
                transmute_copy::<_, _>(&(
                    self.bus_challenge,
                    self.fingerprint_challenge_powers,
                    self.bus_beta,
                ))
            }
        } else {
            assert_eq!(TypeId::of::<NewEF>(), TypeId::of::<EFPacking<EF>>());
            unsafe {
                transmute_copy::<_, _>(&(
                    EFPacking::<EF>::from(self.bus_challenge),
                    self.fingerprint_challenge_powers
                        .map(|c| EFPacking::<EF>::from(c)),
                    EFPacking::<EF>::from(self.bus_beta),
                ))
            }
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
    fn buses() -> Vec<Bus>;
    fn execute(
        arg_a: F,
        arg_b: F,
        arg_c: F,
        aux: usize,
        memory: &mut Memory,
        trace: &mut PrecompileTrace,
        ctx: PrecompileExecutionContext<'_>,
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

#[derive(Debug)]
pub struct PrecompileExecutionContext<'a> {
    pub poseidon16_precomputed: &'a [([F; 16], [F; 16])],
    pub n_poseidon16_precomputed_used: &'a mut usize,
}
