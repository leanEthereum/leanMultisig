use crate::{EF, F, InstructionContext, RunnerError, Table};
use backend::*;

use std::{any::TypeId, cmp::Reverse, collections::BTreeMap, mem::transmute};
use utils::VarCount;

pub type ColIndex = usize;

pub type CommittedStatements = BTreeMap<Table, Vec<(MultilinearPoint<EF>, BTreeMap<ColIndex, EF>)>>;

#[derive(Debug)]
pub struct LookupIntoMemory {
    pub index: ColIndex, // should be in base field columns
    /// For (i, col_index) in values.iter().enumerate(), For j in 0..num_rows, columns_f[col_index][j] = memory[index[j] + i]
    pub values: Vec<ColIndex>,
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

#[derive(Debug, Clone, Copy)]
pub enum BusData {
    Column(ColIndex),
    Constant(usize),
}

#[derive(Debug)]
pub struct Bus {
    pub direction: BusDirection,
    pub selector: ColIndex,
    pub data: Vec<BusData>,
}

#[derive(Debug, Default)]
pub struct TableTrace {
    pub base: Vec<Vec<F>>,
    pub non_padded_n_rows: usize,
    pub log_n_rows: VarCount,
}

impl TableTrace {
    pub fn new<A: TableT>(air: &A) -> Self {
        Self {
            base: vec![Vec::new(); air.n_columns_total()],
            non_padded_n_rows: 0, // filled later
            log_n_rows: 0,        // filled later
        }
    }
}

pub fn sort_tables_by_height(tables_log_heights: &BTreeMap<Table, usize>) -> Vec<(Table, usize)> {
    let mut tables_heights_sorted = tables_log_heights.clone().into_iter().collect::<Vec<_>>();
    tables_heights_sorted.sort_by_key(|&(_, h)| Reverse(h));
    tables_heights_sorted
}

#[derive(Debug, Default)]
pub struct ExtraDataForBuses<EF: ExtensionField<PF<EF>>> {
    // GKR quotient challenges
    pub logup_alphas_eq_poly: Vec<EF>,
    pub logup_alphas_eq_poly_packed: Vec<EFPacking<EF>>,
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
            unsafe { transmute::<(&Vec<EF>, &EF), (&Vec<NewEF>, &NewEF)>((&self.logup_alphas_eq_poly, &self.bus_beta)) }
        } else {
            assert_eq!(TypeId::of::<NewEF>(), TypeId::of::<EFPacking<EF>>());
            unsafe {
                transmute::<(&Vec<EFPacking<EF>>, &EFPacking<EF>), (&Vec<NewEF>, &NewEF)>((
                    &self.logup_alphas_eq_poly_packed,
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
    fn lookups(&self) -> Vec<LookupIntoMemory>;
    fn bus(&self) -> Bus;
    fn padding_row(&self) -> Vec<F>;
    fn execute(
        &self,
        arg_a: F,
        arg_b: F,
        arg_c: F,
        aux_1: usize,
        aux_2: usize,
        ctx: &mut InstructionContext<'_>,
    ) -> Result<(), RunnerError>;

    // number of columns committed + potentially some virtual columns (useful to keep in memory for logup)
    fn n_columns_total(&self) -> usize {
        self.n_columns()
    }

    fn is_execution_table(&self) -> bool {
        false
    }

    fn n_committed_columns(&self) -> usize {
        self.n_columns()
    }

    fn lookup_index_columns<'a>(&'a self, trace: &'a TableTrace) -> Vec<&'a [F]> {
        self.lookups()
            .iter()
            .map(|lookup| &trace.base[lookup.index][..])
            .collect()
    }
    fn lookup_value_columns<'a>(&self, trace: &'a TableTrace) -> Vec<Vec<&'a [F]>> {
        let mut cols = Vec::new();
        for lookup in self.lookups() {
            cols.push(lookup.values.iter().map(|&c| &trace.base[c][..]).collect());
        }
        cols
    }
}
