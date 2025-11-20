use std::{any::TypeId, mem::transmute_copy};

use crate::{EF, F, Memory, RunnerError, Table};
use multilinear_toolkit::prelude::*;
use p3_air::Air;

mod dot_product;
pub use dot_product::*;

mod poseidon_16;
pub use poseidon_16::*;

mod poseidon_24;
pub use poseidon_24::*;

mod multilinear_eval;
pub use multilinear_eval::*;
use sub_protocols::{
    ColDims, ExtensionCommitmentFromBaseProver, ExtensionCommitmentFromBaseVerifier,
    committed_dims_extension_from_base,
};

pub type ColIndex = usize;

#[derive(Debug)]
pub struct LookupIntoMemory {
    pub index: ColIndex, // should be in base field columns
    pub values: ColIndex,
}

#[derive(Debug)]
pub struct ExtensionFieldLookupIntoMemory {
    pub index: ColIndex, // should be in base field columns
    pub values: ColIndex,
}

#[derive(Debug)]
pub struct VectorLookupIntoMemory {
    pub index: ColIndex, // should be in base field columns
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
    fn commited_columns_f() -> Vec<ColIndex>;
    /// the first committed column in the extension starts at index 0
    fn commited_columns_ef() -> Vec<ColIndex>;
    fn normal_lookups_f() -> Vec<LookupIntoMemory>;
    fn normal_lookups_ef() -> Vec<ExtensionFieldLookupIntoMemory>;
    fn vector_lookups() -> Vec<VectorLookupIntoMemory>;
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
    fn committed_dims(n_rows: usize) -> Vec<ColDims<F>> {
        let mut dims = Self::commited_columns_f()
            .iter()
            .map(|&c| ColDims::padded(n_rows, Self::padding_row()[c].as_base().unwrap()))
            .collect::<Vec<_>>();
        dims.extend(committed_dims_extension_from_base(
            n_rows,
            Self::commited_columns_ef()
                .iter()
                .map(|&c| Self::padding_row()[Self::n_columns_f() + c])
                .collect(),
        ));
        dims
    }
    fn committed_statements_prover(
        prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
        air_point: &MultilinearPoint<EF>,
        air_values: &[EF],
        ext_commitment_helper: &ExtensionCommitmentFromBaseProver<EF>,
        normal_lookup_statements_on_indexes: &mut Vec<Vec<Evaluation<EF>>>,
    ) -> Vec<Vec<Evaluation<EF>>> {
        assert_eq!(air_values.len(), Self::n_columns());

        let mut statements = Self::commited_columns_f()
            .iter()
            .map(|&c| vec![Evaluation::new(air_point.clone(), air_values[c].clone())])
            .collect::<Vec<_>>();
        statements.extend(ext_commitment_helper.after_commitment(prover_state, air_point));

        for lookup in Self::normal_lookups_f() {
            statements[lookup.index].extend(normal_lookup_statements_on_indexes.remove(0));
        }
        for lookup in Self::normal_lookups_ef() {
            statements[lookup.index].extend(normal_lookup_statements_on_indexes.remove(0));
        }

        statements
    }
    fn committed_statements_verifier(
        verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
        air_point: &MultilinearPoint<EF>,
        air_values: &[EF],
        normal_lookup_statements_on_indexes: &mut Vec<Vec<Evaluation<EF>>>,
    ) -> ProofResult<Vec<Vec<Evaluation<EF>>>> {
        assert_eq!(air_values.len(), Self::n_columns());

        let mut statements = Self::commited_columns_f()
            .iter()
            .map(|&c| vec![Evaluation::new(air_point.clone(), air_values[c].clone())])
            .collect::<Vec<_>>();

        statements.extend(ExtensionCommitmentFromBaseVerifier::after_commitment(
            verifier_state,
            &MultiEvaluation::new(
                air_point.clone(),
                Self::commited_columns_ef()
                    .iter()
                    .map(|&c| air_values[Self::n_columns_f() + c].clone())
                    .collect::<Vec<_>>(),
            ),
        )?);
        for lookup in Self::normal_lookups_f() {
            statements[lookup.index].extend(normal_lookup_statements_on_indexes.remove(0));
        }
        for lookup in Self::normal_lookups_ef() {
            statements[lookup.index].extend(normal_lookup_statements_on_indexes.remove(0));
        }

        Ok(statements)
    }
    fn normal_lookups_statements(
        air_point: &MultilinearPoint<EF>,
        air_values: &[EF],
    ) -> Vec<Vec<Evaluation<EF>>> {
        assert_eq!(air_values.len(), Self::n_columns());

        let mut statements = Vec::new();
        for lookup in Self::normal_lookups_f() {
            statements.push(vec![Evaluation::new(
                air_point.clone(),
                air_values[lookup.values].clone(),
            )]);
        }
        for lookup in Self::normal_lookups_ef() {
            statements.push(vec![Evaluation::new(
                air_point.clone(),
                air_values[lookup.values + Self::n_columns_f()].clone(),
            )]);
        }
        statements
    }
    fn committed_columns<'a>(
        trace: &'a PrecompileTrace,
        computation_ext_to_base_helper: &'a ExtensionCommitmentFromBaseProver<EF>,
    ) -> Vec<&'a [PF<EF>]> {
        // base field committed columns
        let mut cols = Self::commited_columns_f()
            .iter()
            .map(|&c| &trace.base[c][..])
            .collect::<Vec<_>>();
        // convert extension field committed columns to base field
        cols.extend(
            computation_ext_to_base_helper
                .sub_columns_to_commit
                .iter()
                .map(Vec::as_slice),
        );
        cols
    }
    fn normal_lookup_index_columns(trace: &PrecompileTrace) -> Vec<&[PF<EF>]> {
        let mut cols = Vec::new();
        for lookup in Self::normal_lookups_f() {
            cols.push(&trace.base[lookup.index][..]);
        }
        for lookup in Self::normal_lookups_ef() {
            cols.push(&trace.base[lookup.index][..]);
        }
        cols
    }
    fn num_normal_lookups() -> usize {
        Self::normal_lookups_f().len() + Self::normal_lookups_ef().len()
    }
    fn vector_lookup_index_columns(trace: &PrecompileTrace) -> Vec<&[PF<EF>]> {
        let mut cols = Vec::new();
        for lookup in Self::vector_lookups() {
            for &value_col in &lookup.values {
                cols.push(&trace.base[value_col][..]);
            }
        }
        cols
    }
    fn normal_lookup_f_value_columns(trace: &PrecompileTrace) -> Vec<&[PF<EF>]> {
        let mut cols = Vec::new();
        for lookup in Self::normal_lookups_f() {
            cols.push(&trace.base[lookup.values][..]);
        }
        cols
    }
    fn normal_lookup_ef_value_columns(trace: &PrecompileTrace) -> Vec<&[EF]> {
        let mut cols = Vec::new();
        for lookup in Self::normal_lookups_ef() {
            cols.push(&trace.ext[lookup.values][..]);
        }
        cols
    }
}

#[derive(Debug)]
pub struct PrecompileExecutionContext<'a> {
    pub poseidon16_precomputed: &'a [([F; 16], [F; 16])],
    pub n_poseidon16_precomputed_used: &'a mut usize,
    pub poseidon24_precomputed: &'a [([F; 24], [F; 8])],
    pub n_poseidon24_precomputed_used: &'a mut usize,
    pub multilinear_evals_witness: &'a mut Vec<WitnessMultilinearEval>,
}
