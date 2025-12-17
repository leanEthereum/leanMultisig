use crate::{
    COL_INDEX_FP, COL_INDEX_MEM_ADDRESS_A, COL_INDEX_MEM_ADDRESS_B, COL_INDEX_MEM_ADDRESS_C, COL_INDEX_MEM_VALUE_A,
    COL_INDEX_MEM_VALUE_B, COL_INDEX_MEM_VALUE_C, COL_INDEX_PC, DIMENSION, EF, F, InstructionContext, RunnerError,
    Table,
};
use multilinear_toolkit::prelude::*;

use std::{any::TypeId, mem::transmute};
use utils::VarCount;

use sub_protocols::{ExtensionCommitmentFromBaseProver, ExtensionCommitmentFromBaseVerifier};

// Zero padding will be added to each at least, if this minimum is not reached
// (ensuring AIR / GKR work fine, with SIMD, without too much edge cases)
// Long term, we should find a more elegant solution.
pub const MIN_LOG_N_ROWS_PER_TABLE: usize = 8;
pub const MAX_LOG_N_ROWS_PER_TABLE: usize = 100; // Avoid "DOS attack"

pub type ColIndex = usize;

#[derive(Debug)]
pub struct LookupIntoMemory {
    pub index: ColIndex, // should be in base field columns
    /// For (i, col_index) in values.iter().enumerate(), For j in 0..num_rows, columns_f[col_index][j] = memory[index[j] + i]
    pub values: Vec<ColIndex>,
}

#[derive(Debug)]
pub struct ExtensionFieldLookupIntoMemory {
    pub index: ColIndex, // should be in base field columns
    pub values: ColIndex,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BusDirection {
    Pull,
    Push,
}

impl BusDirection {
    pub fn to_field_flag(self) -> F {
        match self {
            BusDirection::Pull => F::NEG_ONE,
            BusDirection::Push => F::ONE,
        }
    }
}

#[derive(Debug)]
pub struct Bus {
    pub direction: BusDirection,
    pub table: BusTable,
    pub selector: ColIndex,
    pub data: Vec<ColIndex>, // For now, we only supports F (base field) columns as bus data
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum BusTable {
    Constant(Table),
    Variable(ColIndex),
}

#[derive(Debug, Default)]
pub struct TableTrace {
    pub base: Vec<Vec<F>>,
    pub ext: Vec<Vec<EF>>,
    pub log_n_rows: VarCount,
}

impl TableTrace {
    pub fn new<A: TableT>(air: &A) -> Self {
        Self {
            base: vec![Vec::new(); air.n_columns_f_total()],
            ext: vec![Vec::new(); air.n_columns_ef_total()],
            log_n_rows: 0, // filled later
        }
    }
}

#[derive(Debug, Default)]
pub struct ExtraDataForBuses<EF: ExtensionField<PF<EF>>> {
    // GKR quotient challenges
    pub fingerprint_challenge_powers: Vec<EF>,
    pub fingerprint_challenge_powers_packed: Vec<EFPacking<EF>>,
    pub bus_beta: EF,
    pub bus_beta_packed: EFPacking<EF>,
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
    pub fn transmute_bus_data<NewEF: 'static>(&self) -> (&Vec<NewEF>, &NewEF) {
        if TypeId::of::<NewEF>() == TypeId::of::<EF>() {
            unsafe {
                transmute::<(&Vec<EF>, &EF), (&Vec<NewEF>, &NewEF)>((
                    &self.fingerprint_challenge_powers,
                    &self.bus_beta,
                ))
            }
        } else {
            assert_eq!(TypeId::of::<NewEF>(), TypeId::of::<EFPacking<EF>>());
            unsafe {
                transmute::<(&Vec<EFPacking<EF>>, &EFPacking<EF>), (&Vec<NewEF>, &NewEF)>((
                    &self.fingerprint_challenge_powers_packed,
                    &self.bus_beta_packed,
                ))
            }
        }
    }
}

/// Convention: The "AIR" columns are at the start (both for base and extension columns).
/// (Some columns may not appear in the AIR)
pub trait TableT: Air {
    fn name(&self) -> &'static str;
    fn identifier(&self) -> Table;
    fn lookups_f(&self) -> Vec<LookupIntoMemory>;
    fn ookups_ef(&self) -> Vec<ExtensionFieldLookupIntoMemory>;
    fn buses(&self) -> Vec<Bus>;
    fn padding_row_f(&self) -> Vec<F>;
    fn padding_row_ef(&self) -> Vec<EF>;
    fn execute(
        &self,
        arg_a: F,
        arg_b: F,
        arg_c: F,
        aux: usize,
        ctx: &mut InstructionContext<'_>,
    ) -> Result<(), RunnerError>;

    fn n_columns_f_total(&self) -> usize {
        // by default, we assume all the columns are used in AIR
        self.n_columns_f_air()
    }
    fn n_columns_ef_total(&self) -> usize {
        // by default, we assume all the columns are used in AIR
        self.n_columns_ef_air()
    }

    fn air_padding_row_f(&self) -> Vec<F> {
        // only the shited_columns
        self.down_column_indexes_f()
            .into_iter()
            .map(|i| self.padding_row_f()[i])
            .collect()
    }
    fn air_padding_row_ef(&self) -> Vec<EF> {
        // only the shited_columns
        self.down_column_indexes_ef()
            .into_iter()
            .map(|i| self.padding_row_ef()[i])
            .collect()
    }
    fn commited_columns_f(&self) -> Vec<ColIndex> {
        if self.identifier() == Table::execution() {
            vec![
                COL_INDEX_PC,
                COL_INDEX_FP,
                COL_INDEX_MEM_ADDRESS_A,
                COL_INDEX_MEM_ADDRESS_B,
                COL_INDEX_MEM_ADDRESS_C,
                COL_INDEX_MEM_VALUE_A,
                COL_INDEX_MEM_VALUE_B,
                COL_INDEX_MEM_VALUE_C,
            ]
        } else {
            (0..self.n_columns_f_air()).collect()
        }
    }
    fn commited_columns_ef(&self) -> Vec<ColIndex> {
        (0..self.n_columns_ef_air()).collect()
    }
    fn committed_dims(&self, log_n_rows: usize) -> Vec<VarCount> {
        vec![log_n_rows; self.n_commited_columns_f() + self.n_commited_columns_ef() * DIMENSION]
    }
    fn n_commited_columns_f(&self) -> usize {
        self.commited_columns_f().len()
    }
    fn n_commited_columns_ef(&self) -> usize {
        self.commited_columns_ef().len()
    }

    #[allow(clippy::too_many_arguments)]
    fn committed_statements_prover(
        &self,
        prover_state: &mut impl FSProver<EF>,
        air_point: &MultilinearPoint<EF>,
        air_values_f: &[EF],
        ext_commitment_helper: Option<&ExtensionCommitmentFromBaseProver<EF>>,
        lokup_statements_on_indexes_f: &mut Vec<Evaluation<EF>>,
        lookup_statements_on_indexes_ef: &mut Vec<Evaluation<EF>>,
        lookup_statements_on_values_f: &mut Vec<Vec<Evaluation<EF>>>,
        lookup_statements_on_values_ef: &mut Vec<[Evaluation<EF>; DIMENSION]>,
    ) -> Vec<Vec<Evaluation<EF>>> {
        assert_eq!(air_values_f.len(), self.n_columns_f_air());

        let mut statements = self
            .commited_columns_f()
            .iter()
            .map(|&c| vec![Evaluation::new(air_point.clone(), air_values_f[c])])
            .collect::<Vec<_>>();
        if let Some(ext_commitment_helper) = ext_commitment_helper {
            statements.extend(ext_commitment_helper.after_commitment(prover_state, air_point));
        }

        for lookup in self.lookups_f() {
            statements[self.find_committed_column_index_f(lookup.index)].push(lokup_statements_on_indexes_f.remove(0));
        }
        for lookup in self.ookups_ef() {
            statements[self.find_committed_column_index_f(lookup.index)]
                .push(lookup_statements_on_indexes_ef.remove(0));
        }

        for lookup in self.lookups_f() {
            for (col_index, col_statements) in lookup
                .values
                .iter()
                .zip(lookup_statements_on_values_f.remove(0).into_iter())
            {
                statements[self.find_committed_column_index_f(*col_index)].push(col_statements);
            }
        }
        for lookup in self.ookups_ef() {
            let my_statements = &mut statements
                [self.n_commited_columns_f() + DIMENSION * self.find_committed_column_index_ef(lookup.values)..]
                [..DIMENSION];
            my_statements
                .iter_mut()
                .zip(lookup_statements_on_values_ef.remove(0).into_iter())
                .for_each(|(stmt, to_add)| {
                    stmt.push(to_add);
                });
        }

        statements
    }

    #[allow(clippy::too_many_arguments)]
    fn committed_statements_verifier(
        &self,
        verifier_state: &mut impl FSVerifier<EF>,
        air_point: &MultilinearPoint<EF>,
        air_values_f: &[EF],
        air_values_ef: &[EF],
        lookup_statements_on_indexes_f: &mut Vec<Evaluation<EF>>,
        lookup_statements_on_indexes_ef: &mut Vec<Evaluation<EF>>,
        lookup_statements_on_values_f: &mut Vec<Vec<Evaluation<EF>>>,
        lookup_statements_on_values_ef: &mut Vec<[Evaluation<EF>; DIMENSION]>,
    ) -> ProofResult<Vec<Vec<Evaluation<EF>>>> {
        assert_eq!(air_values_f.len(), self.n_columns_f_air());
        assert_eq!(air_values_ef.len(), self.n_columns_ef_air());

        let mut statements = self
            .commited_columns_f()
            .iter()
            .map(|&c| vec![Evaluation::new(air_point.clone(), air_values_f[c])])
            .collect::<Vec<_>>();

        if self.n_commited_columns_ef() > 0 {
            statements.extend(ExtensionCommitmentFromBaseVerifier::after_commitment(
                verifier_state,
                &MultiEvaluation::new(
                    air_point.clone(),
                    self.commited_columns_ef()
                        .iter()
                        .map(|&c| air_values_ef[c])
                        .collect::<Vec<_>>(),
                ),
            )?);
        }
        for lookup in self.lookups_f() {
            statements[self.find_committed_column_index_f(lookup.index)].push(lookup_statements_on_indexes_f.remove(0));
        }
        for lookup in self.ookups_ef() {
            statements[self.find_committed_column_index_f(lookup.index)]
                .push(lookup_statements_on_indexes_ef.remove(0));
        }

        for lookup in self.lookups_f() {
            for (col_index, col_statements) in lookup
                .values
                .iter()
                .zip(lookup_statements_on_values_f.remove(0).into_iter())
            {
                statements[self.find_committed_column_index_f(*col_index)].push(col_statements);
            }
        }
        for lookup in self.ookups_ef() {
            let my_statements = &mut statements
                [self.n_commited_columns_f() + DIMENSION * self.find_committed_column_index_ef(lookup.values)..]
                [..DIMENSION];
            my_statements
                .iter_mut()
                .zip(lookup_statements_on_values_ef.remove(0).into_iter())
                .for_each(|(stmt, to_add)| {
                    stmt.push(to_add);
                });
        }

        Ok(statements)
    }
    fn committed_columns<'a>(
        &self,
        trace: &'a TableTrace,
        computation_ext_to_base_helper: Option<&'a ExtensionCommitmentFromBaseProver<EF>>,
    ) -> Vec<&'a [F]> {
        // base field committed columns
        let mut cols = self
            .commited_columns_f()
            .iter()
            .map(|&c| &trace.base[c][..])
            .collect::<Vec<_>>();
        // convert extension field committed columns to base field
        if let Some(computation_ext_to_base_helper) = computation_ext_to_base_helper {
            cols.extend(
                computation_ext_to_base_helper
                    .sub_columns_to_commit
                    .iter()
                    .map(Vec::as_slice),
            );
        }
        cols
    }
    fn lookup_index_columns_f<'a>(&'a self, trace: &'a TableTrace) -> Vec<&'a [F]> {
        self.lookups_f()
            .iter()
            .map(|lookup| &trace.base[lookup.index][..])
            .collect()
    }
    fn lookup_index_columns_ef<'a>(&'a self, trace: &'a TableTrace) -> Vec<&'a [F]> {
        self.ookups_ef()
            .iter()
            .map(|lookup| &trace.base[lookup.index][..])
            .collect()
    }
    fn num_lookups_f(&self) -> usize {
        self.lookups_f().len()
    }
    fn num_lookups_ef(&self) -> usize {
        self.ookups_ef().len()
    }
    fn num_buses(&self) -> usize {
        self.buses().len()
    }
    fn lookup_f_value_columns<'a>(&self, trace: &'a TableTrace) -> Vec<Vec<&'a [F]>> {
        let mut cols = Vec::new();
        for lookup in self.lookups_f() {
            cols.push(lookup.values.iter().map(|&c| &trace.base[c][..]).collect());
        }
        cols
    }
    fn lookup_ef_value_columns<'a>(&self, trace: &'a TableTrace) -> Vec<&'a [EF]> {
        let mut cols = Vec::new();
        for lookup in self.ookups_ef() {
            cols.push(&trace.ext[lookup.values][..]);
        }
        cols
    }
    fn find_committed_column_index_f(&self, col: ColIndex) -> usize {
        self.commited_columns_f().iter().position(|&c| c == col).unwrap()
    }
    fn find_committed_column_index_ef(&self, col: ColIndex) -> usize {
        self.commited_columns_ef().iter().position(|&c| c == col).unwrap()
    }
}

pub fn finger_print<F: Field, EF: ExtensionField<F>>(table: F, data: &[F], challenge: EF) -> EF {
    dot_product::<EF, _, _>(challenge.powers().skip(1), data.iter().copied()) + table
}
