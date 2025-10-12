use std::{any::TypeId, marker::PhantomData, mem::transmute};

use p3_air::BaseAir;
use p3_field::{ExtensionField, Field};

use multilinear_toolkit::prelude::*;
use p3_matrix::dense::RowMajorMatrixView;
use tracing::instrument;
use utils::{ConstraintChecker, ConstraintCounter};

use crate::{NormalAir, PackedAir};

#[derive(Debug)]
pub struct AirTable<EF: Field, A, AP> {
    pub air: A,
    pub air_packed: AP,
    pub n_constraints: usize,

    _phantom: std::marker::PhantomData<EF>,
}

impl<EF: ExtensionField<PF<EF>>, A: NormalAir<EF>, AP: PackedAir<EF>> AirTable<EF, A, AP> {
    pub fn new(air: A, air_packed: AP) -> Self {
        tracing::warn!("TODO Double-check that the number of constraints is correct, again");
        let n_constraints = Self::count_num_constraints(&air);
        Self {
            air,
            air_packed,
            n_constraints,
            _phantom: std::marker::PhantomData,
        }
    }

    pub fn n_columns(&self) -> usize {
        <A as BaseAir<PF<EF>>>::width_f(&self.air) + <A as BaseAir<PF<EF>>>::width_ef(&self.air)
    }

    #[instrument(name = "Check trace validity", skip_all)]
    pub fn check_trace_validity<IF: ExtensionField<PF<EF>>>(
        &self,
        witness_f: &[&[IF]],
        witness_ef: &[&[EF]],
    ) -> Result<(), String>
    where
        EF: ExtensionField<IF>,
    {
        let n_rows = witness_f[0].len();
        assert!(
            witness_f.iter().all(|col| col.len() == n_rows)
                && witness_ef.iter().all(|col| col.len() == n_rows)
        );
        if witness_f.len() + witness_ef.len() != self.n_columns() {
            return Err("Invalid number of columns".to_string());
        }
        let handle_errors = |row: usize, constraint_checker: &mut ConstraintChecker<'_, IF, EF>| {
            if !constraint_checker.errors.is_empty() {
                return Err(format!(
                    "Trace is not valid at row {}: contraints not respected: {}",
                    row,
                    constraint_checker
                        .errors
                        .iter()
                        .map(|e| e.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                ));
            }
            Ok(())
        };
        if <A as BaseAir<PF<EF>>>::structured(&self.air) {
            for row in 0..n_rows - 1 {
                let up_f = (0..witness_f.len())
                    .map(|j| witness_f[j][row])
                    .collect::<Vec<_>>();
                let down_f = (0..witness_f.len())
                    .map(|j| witness_f[j][row + 1])
                    .collect::<Vec<_>>();
                let up_ef = (0..witness_ef.len())
                    .map(|j| witness_ef[j][row])
                    .collect::<Vec<_>>();
                let down_ef = (0..witness_ef.len())
                    .map(|j| witness_ef[j][row + 1])
                    .collect::<Vec<_>>();
                let up_and_down_f = [up_f, down_f].concat();
                let up_and_down_ef = [up_ef, down_ef].concat();
                let mut constraints_checker = ConstraintChecker::<IF, EF> {
                    main: (
                        RowMajorMatrixView::new(&up_and_down_f, witness_f.len()),
                        RowMajorMatrixView::new(&up_and_down_ef, witness_ef.len()),
                    ),
                    constraint_index: 0,
                    errors: Vec::new(),
                    field: PhantomData,
                };
                if TypeId::of::<IF>() == TypeId::of::<EF>() {
                    unsafe {
                        self.air.eval(transmute::<
                            &mut ConstraintChecker<'_, IF, EF>,
                            &mut ConstraintChecker<'_, EF, EF>,
                        >(&mut constraints_checker));
                    }
                } else {
                    assert_eq!(TypeId::of::<IF>(), TypeId::of::<PF<EF>>());
                    unsafe {
                        self.air.eval(transmute::<
                            &mut ConstraintChecker<'_, IF, EF>,
                            &mut ConstraintChecker<'_, PF<EF>, EF>,
                        >(&mut constraints_checker));
                    }
                }
                handle_errors(row, &mut constraints_checker)?;
            }
        } else {
            #[allow(clippy::needless_range_loop)]
            for row in 0..n_rows {
                let up_f = (0..witness_f.len())
                    .map(|j| witness_f[j][row])
                    .collect::<Vec<_>>();
                let up_ef = (0..witness_ef.len())
                    .map(|j| witness_ef[j][row])
                    .collect::<Vec<_>>();
                let mut constraints_checker = ConstraintChecker {
                    main: (
                        RowMajorMatrixView::new(&up_f, witness_f.len()),
                        RowMajorMatrixView::new(&up_ef, witness_ef.len()),
                    ),
                    constraint_index: 0,
                    errors: Vec::new(),
                    field: PhantomData,
                };
                if TypeId::of::<IF>() == TypeId::of::<EF>() {
                    unsafe {
                        self.air.eval(transmute::<
                            &mut ConstraintChecker<'_, IF, EF>,
                            &mut ConstraintChecker<'_, EF, EF>,
                        >(&mut constraints_checker));
                    }
                } else {
                    assert_eq!(TypeId::of::<IF>(), TypeId::of::<PF<EF>>());
                    unsafe {
                        self.air.eval(transmute::<
                            &mut ConstraintChecker<'_, IF, EF>,
                            &mut ConstraintChecker<'_, PF<EF>, EF>,
                        >(&mut constraints_checker));
                    }
                }
                handle_errors(row, &mut constraints_checker)?;
            }
        }
        Ok(())
    }

    pub fn count_num_constraints(air: &A) -> usize {
        let mut constraints_checker = ConstraintCounter::<EF> {
            num_constraints: 0,
            structured: <A as BaseAir<PF<EF>>>::structured(air),
            ext_field: PhantomData,
            width_f: <A as BaseAir<PF<EF>>>::width_f(air),
            width_ef: <A as BaseAir<PF<EF>>>::width_ef(air),
        };
        air.eval(&mut constraints_checker);
        constraints_checker.num_constraints
    }
}
