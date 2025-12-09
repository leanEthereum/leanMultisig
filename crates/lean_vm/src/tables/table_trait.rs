use crate::{
    COL_INDEX_FP, COL_INDEX_MEM_ADDRESS_A, COL_INDEX_MEM_ADDRESS_B, COL_INDEX_MEM_ADDRESS_C, COL_INDEX_MEM_VALUE_A,
    COL_INDEX_MEM_VALUE_B, COL_INDEX_MEM_VALUE_C, COL_INDEX_PC, DIMENSION, EF, F, InstructionContext, RunnerError,
    Table, VECTOR_LEN,
};
use multilinear_toolkit::prelude::*;

use std::{any::TypeId, array, mem::transmute};
use utils::ToUsize;

use sub_protocols::{
    ColDims, ExtensionCommitmentFromBaseProver, ExtensionCommitmentFromBaseVerifier, committed_dims_extension_from_base,
};

// Zero padding will be added to each at least, if this minimum is not reached
// (ensuring AIR / GKR work fine, with SIMD, without too much edge cases)
// Long term, we should find a more elegant solution.
pub const MIN_LOG_N_ROWS_PER_TABLE: usize = 8;
pub const MIN_N_ROWS_PER_TABLE: usize = 1 << MIN_LOG_N_ROWS_PER_TABLE;

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
pub enum BusSelector {
    Column(ColIndex),
    ConstantOne,
}

#[derive(Debug)]
pub struct Bus {
    pub direction: BusDirection,
    pub table: BusTable,
    pub selector: BusSelector,
    pub data: Vec<ColIndex>, // For now, we only supports F (base field) columns as bus data
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum BusTable {
    Constant(Table),
    Variable(ColIndex),
}

#[derive(Debug, Clone, Copy, Default)]
pub struct TableHeight(pub usize);

impl TableHeight {
    pub fn n_rows_non_padded(self) -> usize {
        self.0
    }
    pub fn n_rows_non_padded_maxed(self) -> usize {
        self.0.max(MIN_N_ROWS_PER_TABLE)
    }
    pub fn n_rows_padded(self) -> usize {
        self.0.next_power_of_two().max(MIN_N_ROWS_PER_TABLE)
    }
    pub fn padding_len(self) -> usize {
        self.n_rows_padded() - self.0
    }
    pub fn log_padded(self) -> usize {
        log2_strict_usize(self.n_rows_padded())
    }
}

#[derive(Debug, Default, derive_more::Deref)]
pub struct TableTrace {
    pub base: Vec<Vec<F>>,
    pub ext: Vec<Vec<EF>>,
    #[deref]
    pub height: TableHeight,
}

impl TableTrace {
    pub fn new<A: TableT>(air: &A) -> Self {
        Self {
            base: vec![Vec::new(); air.n_columns_f_total()],
            ext: vec![Vec::new(); air.n_columns_ef_total()],
            height: TableHeight::default(), // filled later
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
    fn normal_lookups_f(&self) -> Vec<LookupIntoMemory>;
    fn normal_lookups_ef(&self) -> Vec<ExtensionFieldLookupIntoMemory>;
    fn vector_lookups(&self) -> Vec<VectorLookupIntoMemory>;
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
    fn committed_dims(&self, n_rows: usize) -> Vec<ColDims<F>> {
        let mut dims = self
            .commited_columns_f()
            .iter()
            .map(|&c| ColDims::padded(n_rows, self.padding_row_f()[c]))
            .collect::<Vec<_>>();
        dims.extend(committed_dims_extension_from_base(
            n_rows,
            self.commited_columns_ef()
                .iter()
                .map(|&c| self.padding_row_ef()[c])
                .collect(),
        ));
        dims
    }
    fn num_commited_columns_f(&self) -> usize {
        self.commited_columns_f().len()
    }
    fn n_commited_columns_ef(&self) -> usize {
        self.commited_columns_ef().len()
    }

    #[allow(clippy::too_many_arguments)]
    fn committed_statements_prover(
        &self,
        prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
        air_point: &MultilinearPoint<EF>,
        air_values_f: &[EF],
        ext_commitment_helper: Option<&ExtensionCommitmentFromBaseProver<EF>>,
        lokup_statements_on_indexes_f: &mut Vec<Evaluation<EF>>,
        lookup_statements_on_indexes_ef: &mut Vec<Evaluation<EF>>,
        lookup_statements_on_indexes_vec: &mut Vec<Evaluation<EF>>,
        lookup_statements_on_values_f: &mut Vec<Evaluation<EF>>,
        lookup_statements_on_values_ef: &mut Vec<[Evaluation<EF>; DIMENSION]>,
        lookup_statements_on_values_vec: &mut Vec<[Evaluation<EF>; VECTOR_LEN]>,
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

        for lookup in self.normal_lookups_f() {
            statements[self.find_committed_column_index_f(lookup.index)].push(lokup_statements_on_indexes_f.remove(0));
        }
        for lookup in self.normal_lookups_ef() {
            statements[self.find_committed_column_index_f(lookup.index)]
                .push(lookup_statements_on_indexes_ef.remove(0));
        }
        for lookup in self.vector_lookups() {
            statements[self.find_committed_column_index_f(lookup.index)]
                .push(lookup_statements_on_indexes_vec.remove(0));
        }

        for lookup in self.normal_lookups_f() {
            statements[self.find_committed_column_index_f(lookup.values)].push(lookup_statements_on_values_f.remove(0));
        }
        for lookup in self.normal_lookups_ef() {
            let my_statements = &mut statements
                [self.num_commited_columns_f() + DIMENSION * self.find_committed_column_index_ef(lookup.values)..]
                [..DIMENSION];
            my_statements
                .iter_mut()
                .zip(lookup_statements_on_values_ef.remove(0).into_iter())
                .for_each(|(stmt, to_add)| {
                    stmt.push(to_add);
                });
        }
        for lookup in self.vector_lookups() {
            for (col_index, col_statements) in lookup
                .values
                .iter()
                .zip(lookup_statements_on_values_vec.remove(0).into_iter())
            {
                statements[self.find_committed_column_index_f(*col_index)].push(col_statements);
            }
        }

        statements
    }

    #[allow(clippy::too_many_arguments)]
    fn committed_statements_verifier(
        &self,
        verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
        air_point: &MultilinearPoint<EF>,
        air_values_f: &[EF],
        air_values_ef: &[EF],
        lookup_statements_on_indexes_f: &mut Vec<Evaluation<EF>>,
        lookup_statements_on_indexes_ef: &mut Vec<Evaluation<EF>>,
        lookup_statements_on_indexes_vec: &mut Vec<Evaluation<EF>>,
        lookup_statements_on_values_f: &mut Vec<Evaluation<EF>>,
        lookup_statements_on_values_ef: &mut Vec<[Evaluation<EF>; DIMENSION]>,
        lookup_statements_on_values_vec: &mut Vec<[Evaluation<EF>; VECTOR_LEN]>,
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
        for lookup in self.normal_lookups_f() {
            statements[self.find_committed_column_index_f(lookup.index)].push(lookup_statements_on_indexes_f.remove(0));
        }
        for lookup in self.normal_lookups_ef() {
            statements[self.find_committed_column_index_f(lookup.index)]
                .push(lookup_statements_on_indexes_ef.remove(0));
        }
        for lookup in self.vector_lookups() {
            statements[self.find_committed_column_index_f(lookup.index)]
                .push(lookup_statements_on_indexes_vec.remove(0));
        }

        for lookup in self.normal_lookups_f() {
            statements[self.find_committed_column_index_f(lookup.values)].push(lookup_statements_on_values_f.remove(0));
        }
        for lookup in self.normal_lookups_ef() {
            let my_statements = &mut statements
                [self.num_commited_columns_f() + DIMENSION * self.find_committed_column_index_ef(lookup.values)..]
                [..DIMENSION];
            my_statements
                .iter_mut()
                .zip(lookup_statements_on_values_ef.remove(0).into_iter())
                .for_each(|(stmt, to_add)| {
                    stmt.push(to_add);
                });
        }
        for lookup in self.vector_lookups() {
            for (col_index, col_statements) in lookup
                .values
                .iter()
                .zip(lookup_statements_on_values_vec.remove(0).into_iter())
            {
                statements[self.find_committed_column_index_f(*col_index)].push(col_statements);
            }
        }

        Ok(statements)
    }
    fn normal_lookups_statements_f(
        &self,
        air_point: &MultilinearPoint<EF>,
        air_values_f: &[EF],
    ) -> Vec<Vec<Evaluation<EF>>> {
        assert_eq!(air_values_f.len(), self.n_columns_f_air());
        let mut statements = Vec::new();
        for lookup in self.normal_lookups_f() {
            statements.push(vec![Evaluation::new(air_point.clone(), air_values_f[lookup.values])]);
        }
        statements
    }
    fn normal_lookups_statements_ef(
        &self,
        air_point: &MultilinearPoint<EF>,
        air_values_ef: &[EF],
    ) -> Vec<Vec<Evaluation<EF>>> {
        assert_eq!(air_values_ef.len(), self.n_columns_ef_air());
        let mut statements = Vec::new();
        for lookup in self.normal_lookups_ef() {
            statements.push(vec![Evaluation::new(air_point.clone(), air_values_ef[lookup.values])]);
        }
        statements
    }
    fn vectorized_lookups_statements(
        &self,
        air_point: &MultilinearPoint<EF>,
        air_values_f: &[EF],
    ) -> Vec<Vec<MultiEvaluation<EF>>> {
        assert_eq!(air_values_f.len(), self.n_columns_f_air());
        let mut statements = Vec::new();
        for lookup in self.vector_lookups() {
            statements.push(vec![MultiEvaluation::new(
                air_point.clone(),
                lookup.values.map(|col| air_values_f[col]).to_vec(),
            )]);
        }
        statements
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
    fn normal_lookup_index_columns_f<'a>(&'a self, trace: &'a TableTrace) -> Vec<&'a [F]> {
        self.normal_lookups_f()
            .iter()
            .map(|lookup| &trace.base[lookup.index][..])
            .collect()
    }
    fn normal_lookup_index_columns_ef<'a>(&'a self, trace: &'a TableTrace) -> Vec<&'a [F]> {
        self.normal_lookups_ef()
            .iter()
            .map(|lookup| &trace.base[lookup.index][..])
            .collect()
    }
    fn vector_lookup_index_columns<'a>(&self, trace: &'a TableTrace) -> Vec<&'a [F]> {
        let mut cols = Vec::new();
        for lookup in self.vector_lookups() {
            cols.push(&trace.base[lookup.index][..]);
        }
        cols
    }
    fn num_normal_lookups_f(&self) -> usize {
        self.normal_lookups_f().len()
    }
    fn num_normal_lookups_ef(&self) -> usize {
        self.normal_lookups_ef().len()
    }
    fn num_vector_lookups(&self) -> usize {
        self.vector_lookups().len()
    }
    fn normal_lookup_f_value_columns<'a>(&self, trace: &'a TableTrace) -> Vec<&'a [F]> {
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
    fn vector_lookup_values_columns<'a>(&self, trace: &'a TableTrace) -> Vec<[&'a [F]; VECTOR_LEN]> {
        let mut cols = Vec::new();
        for lookup in self.vector_lookups() {
            cols.push(array::from_fn(|i| &trace.base[lookup.values[i]][..]));
        }
        cols
    }
    fn normal_lookup_default_indexes_f(&self) -> Vec<usize> {
        let mut default_indexes = Vec::new();
        for lookup in self.normal_lookups_f() {
            default_indexes.push(self.padding_row_f()[lookup.index].to_usize());
        }
        default_indexes
    }
    fn normal_lookup_default_indexes_ef(&self) -> Vec<usize> {
        let mut default_indexes = Vec::new();
        for lookup in self.normal_lookups_ef() {
            default_indexes.push(self.padding_row_f()[lookup.index].to_usize());
        }
        default_indexes
    }
    fn vector_lookup_default_indexes(&self) -> Vec<usize> {
        let mut default_indexes = Vec::new();
        for lookup in self.vector_lookups() {
            default_indexes.push(self.padding_row_f()[lookup.index].to_usize());
        }
        default_indexes
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

impl Bus {
    pub fn padding_contribution<T: TableT>(
        &self,
        table: &T,
        padding: usize,
        bus_challenge: EF,
        fingerprint_challenge: EF,
    ) -> EF {
        let padding_row_f = table.padding_row_f();
        let default_selector = match &self.selector {
            BusSelector::ConstantOne => F::ONE,
            BusSelector::Column(col) => padding_row_f[*col],
        };
        let default_table = match &self.table {
            BusTable::Constant(t) => F::from_usize(t.index()),
            BusTable::Variable(col) => padding_row_f[*col],
        };
        let default_data = self.data.iter().map(|&col| padding_row_f[col]).collect::<Vec<_>>();
        EF::from(default_selector * self.direction.to_field_flag() * F::from_usize(padding))
            / (bus_challenge + finger_print(default_table, &default_data, fingerprint_challenge))
    }
}
