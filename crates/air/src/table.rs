use std::{any::TypeId, marker::PhantomData, mem::transmute};

use p3_air::BaseAir;

use multilinear_toolkit::prelude::*;
use p3_uni_stark::get_symbolic_constraints;
use tracing::instrument;
use utils::ConstraintChecker;

use crate::MyAir;

#[derive(Debug)]
pub struct AirTable<EF: Field, A> {
    pub air: A,
    pub n_constraints: usize,

    _phantom: std::marker::PhantomData<EF>,
}

impl<EF: ExtensionField<PF<EF>>, A: MyAir<EF>> AirTable<EF, A> {
    pub fn new(air: A) -> Self {
        let symbolic_constraints = get_symbolic_constraints(&air);
        let n_constraints = symbolic_constraints.len();
        let constraint_degree =
            Iterator::max(symbolic_constraints.iter().map(|c| c.degree_multiple())).unwrap();
        assert_eq!(constraint_degree, <A as BaseAir<PF<EF>>>::degree(&air));
        Self {
            air,
            n_constraints,
            _phantom: std::marker::PhantomData,
        }
    }

    pub fn n_columns(&self) -> usize {
        <A as BaseAir<PF<EF>>>::width(&self.air)
    }

    pub fn columns_with_shift(&self) -> Vec<usize> {
        <A as BaseAir<PF<EF>>>::columns_with_shift(&self.air)
    }

    #[instrument(name = "Check trace validity", skip_all)]
    pub fn check_trace_validity<IF: ExtensionField<PF<EF>>>(
        &self,
        witness: &[&[IF]],
        last_row: &[IF],
    ) -> Result<(), String>
    where
        EF: ExtensionField<IF>,
    {
        let n_rows = witness[0].len();
        assert!(witness.iter().all(|col| col.len() == n_rows));
        if witness.len() != self.n_columns() {
            return Err("Invalid number of columns".to_string());
        }
        let handle_errors = |row: usize, constraint_checker: &ConstraintChecker<'_, IF, EF>| {
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
        for row in 0..n_rows - 1 {
            let up = (0..self.n_columns())
                .map(|j| witness[j][row])
                .collect::<Vec<_>>();
            let down = self
                .columns_with_shift()
                .iter()
                .map(|j| witness[*j][row + 1])
                .collect::<Vec<_>>();
            let up_and_down = [up, down].concat();
            let constraints_checker = self.eval_transition::<IF>(&up_and_down);
            handle_errors(row, &constraints_checker)?;
        }
        // last transition:
        let up = (0..self.n_columns())
            .map(|j| witness[j][n_rows - 1])
            .collect::<Vec<_>>();
        assert_eq!(last_row.len(), self.columns_with_shift().len());
        let up_and_down = [up, last_row.to_vec()].concat();
        let constraints_checker = self.eval_transition::<IF>(&up_and_down);
        handle_errors(n_rows - 1, &constraints_checker)?;
        Ok(())
    }

    fn eval_transition<'a, IF: ExtensionField<PF<EF>>>(
        &self,
        up_and_down: &'a [IF],
    ) -> ConstraintChecker<'a, IF, EF>
    where
        EF: ExtensionField<IF>,
    {
        let mut constraints_checker = ConstraintChecker::<IF, EF> {
            main: up_and_down,
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
        constraints_checker
    }
}
