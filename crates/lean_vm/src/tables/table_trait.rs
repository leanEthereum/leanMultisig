use crate::{
    COL_INDEX_FP, COL_INDEX_MEM_ADDRESS_A, COL_INDEX_MEM_ADDRESS_B, COL_INDEX_MEM_ADDRESS_C, COL_INDEX_MEM_VALUE_A,
    COL_INDEX_MEM_VALUE_B, COL_INDEX_MEM_VALUE_C, COL_INDEX_PC, DIMENSION, EF, F, InstructionContext, RunnerError,
    Table,
};
use multilinear_toolkit::prelude::*;

use std::{any::TypeId, collections::BTreeMap, mem::transmute};
use utils::{VarCount, dot_product_with_base};

// Zero padding will be added to each at least, if this minimum is not reached
// (ensuring AIR / GKR work fine, with SIMD, without too much edge cases)
// Long term, we should find a more elegant solution.
pub const MIN_LOG_N_ROWS_PER_TABLE: usize = 8;
pub const MAX_LOG_N_ROWS_PER_TABLE: usize = 30; // To avoid overflow in logup (TODO ensure it's secure)

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
    pub logup_alpha_powers: Vec<EF>,
    pub logup_alpha_powers_packed: Vec<EFPacking<EF>>,
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
            unsafe { transmute::<(&Vec<EF>, &EF), (&Vec<NewEF>, &NewEF)>((&self.logup_alpha_powers, &self.bus_beta)) }
        } else {
            assert_eq!(TypeId::of::<NewEF>(), TypeId::of::<EFPacking<EF>>());
            unsafe {
                transmute::<(&Vec<EFPacking<EF>>, &EFPacking<EF>), (&Vec<NewEF>, &NewEF)>((
                    &self.logup_alpha_powers_packed,
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
    fn table(&self) -> Table;
    fn lookups_f(&self) -> Vec<LookupIntoMemory>;
    fn lookups_ef(&self) -> Vec<ExtensionFieldLookupIntoMemory>;
    fn bus(&self) -> Bus;
    fn padding_row_f(&self) -> Vec<F>;
    fn padding_row_ef(&self) -> Vec<EF>;
    fn execute(
        &self,
        arg_a: F,
        arg_b: F,
        arg_c: F,
        aux_1: usize,
        aux_2: usize,
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
    fn is_execution_table(&self) -> bool {
        false
    }
    fn commited_columns_f(&self) -> Vec<ColIndex> {
        if self.is_execution_table() {
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
        extension_columns_transposed: &[Vec<F>], // commit columns in extension field, via base field PCS
        lookup_statements_f: &BTreeMap<ColIndex, Vec<Evaluation<EF>>>,
        lookup_statements_ef: &BTreeMap<ColIndex, Vec<Evaluation<EF>>>,
    ) -> Vec<Vec<Evaluation<EF>>> {
        assert_eq!(air_values_f.len(), self.n_columns_f_air());
        assert_eq!(lookup_statements_ef.len(), self.num_lookups_ef());

        let mut statements = self
            .commited_columns_f()
            .iter()
            .map(|&c| vec![Evaluation::new(air_point.clone(), air_values_f[c])])
            .collect::<Vec<_>>();
        if self.n_commited_columns_ef() > 0 {
            let statements_for_extension_columns = extension_columns_transposed
                .par_iter()
                .map(|col| col.evaluate(air_point))
                .collect::<Vec<_>>();
            prover_state.add_extension_scalars(&statements_for_extension_columns);
            statements.extend(
                statements_for_extension_columns
                    .iter()
                    .map(|eval| vec![Evaluation::new(air_point.clone(), *eval)]),
            );
        }
        for (col_index, statements_f) in lookup_statements_f {
            statements[self.find_committed_column_index_f(*col_index)].extend(statements_f.clone());
        }

        for (col_index, statements_ef) in lookup_statements_ef {
            let my_statements = &mut statements
                [self.n_commited_columns_f() + DIMENSION * self.find_committed_column_index_ef(*col_index)..]
                [..DIMENSION];
            my_statements.iter_mut().zip(statements_ef).for_each(|(stmt, to_add)| {
                stmt.push(to_add.clone());
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
        lookup_statements_f: &BTreeMap<ColIndex, Vec<Evaluation<EF>>>,
        lookup_statements_ef: &BTreeMap<ColIndex, Vec<Evaluation<EF>>>,
    ) -> ProofResult<Vec<Vec<Evaluation<EF>>>> {
        assert_eq!(air_values_f.len(), self.n_columns_f_air());
        assert_eq!(air_values_ef.len(), self.n_columns_ef_air());

        let mut statements = self
            .commited_columns_f()
            .iter()
            .map(|&c| vec![Evaluation::new(air_point.clone(), air_values_f[c])])
            .collect::<Vec<_>>();

        if self.n_commited_columns_ef() > 0 {
            let sub_evals = verifier_state.next_extension_scalars_vec(DIMENSION * self.commited_columns_ef().len())?;
            for (chunk, claim_value) in sub_evals
                .chunks_exact(DIMENSION)
                .zip(self.commited_columns_ef().iter().map(|&c| air_values_ef[c]))
            {
                if dot_product_with_base(chunk) != claim_value {
                    return Err(ProofError::InvalidProof);
                }
                statements.extend(
                    chunk
                        .iter()
                        .map(|&sub_value| vec![Evaluation::new(air_point.clone(), sub_value)]),
                );
            }
        }
        for (col_index, statements_f) in lookup_statements_f {
            statements[self.find_committed_column_index_f(*col_index)].extend(statements_f.clone());
        }

        for (col_index, statements_ef) in lookup_statements_ef {
            let my_statements = &mut statements
                [self.n_commited_columns_f() + DIMENSION * self.find_committed_column_index_ef(*col_index)..]
                [..DIMENSION];
            my_statements.iter_mut().zip(statements_ef).for_each(|(stmt, to_add)| {
                stmt.push(to_add.clone());
            });
        }

        Ok(statements)
    }
    fn committed_columns<'a>(&self, trace: &'a TableTrace, extension_columns_transposed: &'a [Vec<F>]) -> Vec<&'a [F]> {
        // base field committed columns
        let mut cols = self
            .commited_columns_f()
            .iter()
            .map(|&c| &trace.base[c][..])
            .collect::<Vec<_>>();
        // convert extension field committed columns to base field
        cols.extend(extension_columns_transposed.iter().map(Vec::as_slice));
        cols
    }
    fn lookup_index_columns_f<'a>(&'a self, trace: &'a TableTrace) -> Vec<&'a [F]> {
        self.lookups_f()
            .iter()
            .map(|lookup| &trace.base[lookup.index][..])
            .collect()
    }
    fn lookup_index_columns_ef<'a>(&'a self, trace: &'a TableTrace) -> Vec<&'a [F]> {
        self.lookups_ef()
            .iter()
            .map(|lookup| &trace.base[lookup.index][..])
            .collect()
    }
    fn num_lookups_f(&self) -> usize {
        self.lookups_f().len()
    }
    fn num_lookups_ef(&self) -> usize {
        self.lookups_ef().len()
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
        for lookup in self.lookups_ef() {
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
