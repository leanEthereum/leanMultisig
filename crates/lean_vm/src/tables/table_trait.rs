use crate::{DIMENSION, EF, F, InstructionContext, N_COMMITTED_EXEC_COLUMNS, RunnerError, Table};
use multilinear_toolkit::prelude::*;

use std::{any::TypeId, cmp::Reverse, collections::BTreeMap, mem::transmute};
use utils::VarCount;

// Zero padding will be added to each at least, if this minimum is not reached
// (ensuring AIR / GKR work fine, with SIMD, without too much edge cases)
// Long term, we should find a more elegant solution.
pub const MIN_LOG_N_ROWS_PER_TABLE: usize = 8;
pub const MAX_LOG_N_ROWS_PER_TABLE: usize = 30; // To avoid overflow in logup (TODO ensure it's secure)

pub type ColIndex = usize;

pub type CommittedStatements = BTreeMap<Table, Vec<(MultilinearPoint<EF>, BTreeMap<ColIndex, EF>)>>;

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

    fn n_commited_columns_f(&self) -> usize {
        if self.is_execution_table() {
            N_COMMITTED_EXEC_COLUMNS
        } else {
            self.n_columns_f_air()
        }
    }

    fn n_commited_columns_ef(&self) -> usize {
        self.n_columns_ef_air()
    }

    fn n_commited_columns(&self) -> usize {
        self.n_commited_columns_ef() * DIMENSION + self.n_commited_columns_f()
    }

    fn commited_air_values(&self, air_evals: &[EF]) -> BTreeMap<ColIndex, EF> {
        // the intermidiate columns are not commited
        // (they correspond to decoded instructions, in execution table, obtained via logup* into the bytecode)
        air_evals
            .iter()
            .copied()
            .enumerate()
            .filter(|(i, _)| *i < self.n_commited_columns_f() || *i >= self.n_columns_f_air())
            .collect::<BTreeMap<ColIndex, EF>>()
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
}
