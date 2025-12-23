use crate::{
    COL_INDEX_FP, COL_INDEX_MEM_ADDRESS_A, COL_INDEX_MEM_ADDRESS_B, COL_INDEX_MEM_ADDRESS_C, COL_INDEX_MEM_VALUE_A,
    COL_INDEX_MEM_VALUE_B, COL_INDEX_MEM_VALUE_C, COL_INDEX_PC, DIMENSION, EF, F, InstructionContext, RunnerError,
    Table,
};
use multilinear_toolkit::prelude::*;

use std::{any::TypeId, cmp::Reverse, collections::BTreeMap, mem::transmute};
use utils::{VarCount, dot_product_with_base, transpose_slice_to_basis_coefficients};

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

pub fn sort_tables_by_height(table_heights: &BTreeMap<Table, usize>) -> Vec<(Table, usize)> {
    let mut tables_heights_sorted = table_heights.clone().into_iter().collect::<Vec<_>>();
    tables_heights_sorted.sort_by_key(|&(_, h)| Reverse(h));
    tables_heights_sorted
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

    fn n_commited_columns(&self) -> usize {
        self.commited_columns_f().len() + self.n_columns_ef_air() * DIMENSION
    }

    fn committed_statements_f(
        &self,
        air_point: &MultilinearPoint<EF>,
        air_values_f: &[EF],
        lookup_statements_f: &BTreeMap<ColIndex, Vec<Evaluation<EF>>>,
    ) -> Vec<Vec<Evaluation<EF>>> {
        assert_eq!(air_values_f.len(), self.n_columns_f_air());

        let mut statements = self
            .commited_columns_f()
            .iter()
            .map(|&c| vec![Evaluation::new(air_point.clone(), air_values_f[c])])
            .collect::<Vec<_>>();

        for (col_index, statements_f) in lookup_statements_f {
            statements[self.find_committed_column_index_f(*col_index)].extend(statements_f.clone());
        }

        statements
    }

    fn committed_statements_prover_ef(
        &self,
        prover_state: &mut impl FSProver<EF>,
        air_point: &MultilinearPoint<EF>,
        air_values_ef: &[EF],
        trace: &TableTrace,
        lookup_statements_ef: &BTreeMap<ColIndex, MultiEvaluation<EF>>,
    ) -> Vec<Vec<MultiEvaluation<EF>>> {
        assert_eq!(lookup_statements_ef.len(), self.lookups_ef().len());

        let mut statements = vec![];

        for i in 0..self.n_columns_ef_air() {
            let transposed = transpose_slice_to_basis_coefficients::<F, EF>(&trace.ext[i])
                .iter()
                .map(|base_col| base_col.evaluate(air_point))
                .collect::<Vec<_>>();
            prover_state.add_extension_scalars(&transposed);
            if dot_product_with_base(&transposed) != air_values_ef[i] {
                panic!(); // sanity check
            }
            statements.push(vec![MultiEvaluation::new(air_point.clone(), transposed)]);
        }
        for (col_index, statements_ef) in lookup_statements_ef {
            statements[*col_index].push(statements_ef.clone());
        }

        statements
    }

    fn committed_statements_verifier_ef(
        &self,
        verifier_state: &mut impl FSVerifier<EF>,
        air_point: &MultilinearPoint<EF>,
        air_values_ef: &[EF],
        lookup_statements_ef: &BTreeMap<ColIndex, MultiEvaluation<EF>>,
    ) -> ProofResult<Vec<Vec<MultiEvaluation<EF>>>> {
        assert_eq!(lookup_statements_ef.len(), self.lookups_ef().len());

        let mut statements = vec![];

        for i in 0..self.n_columns_ef_air() {
            let transposed = verifier_state.next_extension_scalars_vec(DIMENSION)?;
            if dot_product_with_base(&transposed) != air_values_ef[i] {
                return Err(ProofError::InvalidProof);
            }
            statements.push(vec![MultiEvaluation::new(air_point.clone(), transposed)]);
        }
        for (col_index, statements_ef) in lookup_statements_ef {
            statements[*col_index].push(statements_ef.clone());
        }

        Ok(statements)
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
}
