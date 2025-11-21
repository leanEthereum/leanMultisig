use crate::{EF, F, InstructionContext, RunnerError, Table, VECTOR_LEN};
use multilinear_toolkit::prelude::*;
use p3_air::Air;
use std::{any::TypeId, array, mem::transmute_copy};
use utils::ToUsize;

use sub_protocols::{
    ColDims, ExtensionCommitmentFromBaseProver, ExtensionCommitmentFromBaseVerifier,
    committed_dims_extension_from_base,
};

pub type ColIndex = usize;

pub const N_PRECOMPILES: usize = 4;
pub const ALL_PRECOMPILES: [Table; N_PRECOMPILES] = [
    Table::dot_product(),
    Table::poseidon16(),
    Table::poseidon24(),
    Table::multilinear_eval(),
];

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
pub struct TableTrace {
    pub base: Vec<Vec<F>>,
    pub ext: Vec<Vec<EF>>,
    pub padding_len: usize,
}

impl TableTrace {
    pub fn new<A: Air>(air: &A) -> Self {
        Self {
            base: vec![Vec::new(); air.n_columns_f()],
            ext: vec![Vec::new(); air.n_columns_ef()],
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

pub trait TableT: Air {
    fn name(&self) -> &'static str;
    fn identifier(&self) -> Table;
    fn commited_columns_f(&self) -> Vec<ColIndex>;
    /// the first committed column in the extension starts at index 0
    fn commited_columns_ef(&self) -> Vec<ColIndex>;
    fn normal_lookups_f(&self) -> Vec<LookupIntoMemory>;
    fn normal_lookups_ef(&self) -> Vec<ExtensionFieldLookupIntoMemory>;
    fn vector_lookups(&self) -> Vec<VectorLookupIntoMemory>;
    fn buses(&self) -> Vec<Bus>;
    fn execute(
        &self,
        arg_a: F,
        arg_b: F,
        arg_c: F,
        aux: usize,
        ctx: &mut InstructionContext<'_>,
    ) -> Result<(), RunnerError>;
    fn padding_row(&self) -> Vec<EF>;

    fn air_padding_row(&self) -> Vec<EF> {
        // only the shited_columns
        self.down_column_indexes()
            .into_iter()
            .map(|i| self.padding_row()[i])
            .collect()
    }
    fn committed_dims(&self, n_rows: usize) -> Vec<ColDims<F>> {
        let mut dims = self
            .commited_columns_f()
            .iter()
            .map(|&c| ColDims::padded(n_rows, self.padding_row()[c].as_base().unwrap()))
            .collect::<Vec<_>>();
        dims.extend(committed_dims_extension_from_base(
            n_rows,
            self.commited_columns_ef()
                .iter()
                .map(|&c| self.padding_row()[self.n_columns_f() + c])
                .collect(),
        ));
        dims
    }
    fn committed_statements_prover(
        &self,
        prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
        air_point: &MultilinearPoint<EF>,
        air_values: &[EF],
        ext_commitment_helper: &ExtensionCommitmentFromBaseProver<EF>,
        normal_lookup_statements_on_indexes: &mut Vec<Vec<Evaluation<EF>>>,
    ) -> Vec<Vec<Evaluation<EF>>> {
        assert_eq!(air_values.len(), self.n_columns());

        let mut statements = self
            .commited_columns_f()
            .iter()
            .map(|&c| vec![Evaluation::new(air_point.clone(), air_values[c].clone())])
            .collect::<Vec<_>>();
        statements.extend(ext_commitment_helper.after_commitment(prover_state, air_point));

        for lookup in self.normal_lookups_f() {
            statements[lookup.index].extend(normal_lookup_statements_on_indexes.remove(0));
        }
        for lookup in self.normal_lookups_ef() {
            statements[lookup.index].extend(normal_lookup_statements_on_indexes.remove(0));
        }

        statements
    }
    fn committed_statements_verifier(
        &self,
        verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
        air_point: &MultilinearPoint<EF>,
        air_values: &[EF],
        normal_lookup_statements_on_indexes: &mut Vec<Vec<Evaluation<EF>>>,
    ) -> ProofResult<Vec<Vec<Evaluation<EF>>>> {
        assert_eq!(air_values.len(), self.n_columns());

        let mut statements = self
            .commited_columns_f()
            .iter()
            .map(|&c| vec![Evaluation::new(air_point.clone(), air_values[c].clone())])
            .collect::<Vec<_>>();

        statements.extend(ExtensionCommitmentFromBaseVerifier::after_commitment(
            verifier_state,
            &MultiEvaluation::new(
                air_point.clone(),
                self.commited_columns_ef()
                    .iter()
                    .map(|&c| air_values[self.n_columns_f() + c].clone())
                    .collect::<Vec<_>>(),
            ),
        )?);
        for lookup in self.normal_lookups_f() {
            statements[lookup.index].extend(normal_lookup_statements_on_indexes.remove(0));
        }
        for lookup in self.normal_lookups_ef() {
            statements[lookup.index].extend(normal_lookup_statements_on_indexes.remove(0));
        }

        Ok(statements)
    }
    fn normal_lookups_statements(
        &self,
        air_point: &MultilinearPoint<EF>,
        air_values: &[EF],
    ) -> Vec<Vec<Evaluation<EF>>> {
        assert_eq!(air_values.len(), self.n_columns());

        let mut statements = Vec::new();
        for lookup in self.normal_lookups_f() {
            statements.push(vec![Evaluation::new(
                air_point.clone(),
                air_values[lookup.values].clone(),
            )]);
        }
        for lookup in self.normal_lookups_ef() {
            statements.push(vec![Evaluation::new(
                air_point.clone(),
                air_values[lookup.values + self.n_columns_f()].clone(),
            )]);
        }
        statements
    }
    fn committed_columns<'a>(
        &self,
        trace: &'a TableTrace,
        computation_ext_to_base_helper: &'a ExtensionCommitmentFromBaseProver<EF>,
    ) -> Vec<&'a [PF<EF>]> {
        // base field committed columns
        let mut cols = self
            .commited_columns_f()
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
    fn normal_lookup_index_columns<'a>(&'a self, trace: &'a TableTrace) -> Vec<&'a [PF<EF>]> {
        let mut cols = Vec::new();
        for lookup in self.normal_lookups_f() {
            cols.push(&trace.base[lookup.index][..]);
        }
        for lookup in self.normal_lookups_ef() {
            cols.push(&trace.base[lookup.index][..]);
        }
        cols
    }
    fn num_normal_lookups(&self) -> usize {
        self.normal_lookups_f().len() + self.normal_lookups_ef().len()
    }
    fn num_vector_lookups(&self) -> usize {
        self.vector_lookups().len()
    }
    fn vector_lookup_index_columns<'a>(&self, trace: &'a TableTrace) -> Vec<&'a [PF<EF>]> {
        let mut cols = Vec::new();
        for lookup in self.vector_lookups() {
            cols.push(&trace.base[lookup.index][..]);
        }
        cols
    }
    fn normal_lookup_f_value_columns<'a>(&self, trace: &'a TableTrace) -> Vec<&'a [PF<EF>]> {
        let mut cols = Vec::new();
        for lookup in self.normal_lookups_f() {
            cols.push(&trace.base[lookup.values][..]);
        }
        cols
    }
    fn normal_lookup_ef_value_columns<'a>(&self, trace: &'a TableTrace) -> Vec<&'a [EF]> {
        let mut cols = Vec::new();
        for lookup in self.normal_lookups_ef() {
            cols.push(&trace.ext[lookup.values][..]);
        }
        cols
    }
    fn vector_lookup_values_columns<'a>(
        &self,
        trace: &'a TableTrace,
    ) -> Vec<[&'a [PF<EF>]; VECTOR_LEN]> {
        let mut cols = Vec::new();
        for lookup in self.vector_lookups() {
            cols.push(array::from_fn(|i| &trace.base[lookup.values[i]][..]));
        }
        cols
    }
    fn vector_lookup_default_indexes(&self) -> Vec<usize> {
        let mut default_indexes = Vec::new();
        for lookup in self.vector_lookups() {
            default_indexes.push(
                <EF as ExtensionField<F>>::as_base(&self.padding_row()[lookup.index])
                    .unwrap()
                    .to_usize(),
            );
        }
        default_indexes
    }
}
