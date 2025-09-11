use std::{any::TypeId, marker::PhantomData, mem::transmute};

use p3_air::BaseAir;
use p3_field::{ExtensionField, Field};

use p3_matrix::dense::RowMajorMatrixView;
use p3_uni_stark::get_symbolic_constraints;
use tracing::instrument;
use utils::{ConstraintChecker, PF};

use crate::{NormalAir, PackedAir, witness::AirWitness};

#[derive(Debug)]
pub struct AirTable<EF: Field, A, AP> {
    pub air: A,
    pub air_packed: AP,
    pub n_constraints: usize,

    _phantom: std::marker::PhantomData<EF>,
}

impl<EF: ExtensionField<PF<EF>>, A: NormalAir<EF>, AP: PackedAir<EF>> AirTable<EF, A, AP> {
    pub fn new(air: A, air_packed: AP) -> Self {
        let symbolic_constraints = get_symbolic_constraints(&air, 0, 0);
        let n_constraints = symbolic_constraints.len();
        let constraint_degree =
            Iterator::max(symbolic_constraints.iter().map(|c| c.degree_multiple())).unwrap();
        assert_eq!(constraint_degree, <A as BaseAir<PF<EF>>>::degree(&air));
        Self {
            air,
            air_packed,
            n_constraints,
            _phantom: std::marker::PhantomData,
        }
    }

    pub fn n_columns(&self) -> usize {
        <A as BaseAir<PF<EF>>>::width(&self.air)
    }

    #[instrument(name = "Check trace validity", skip_all)]
    pub fn check_trace_validity<IF: ExtensionField<PF<EF>>>(
        &self,
        witness: &AirWitness<'_, IF>,
    ) -> Result<(), String>
    where
        EF: ExtensionField<IF>,
    {
        if witness.n_columns() != self.n_columns() {
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
            for row in 0..witness.n_rows() - 1 {
                let up = (0..self.n_columns())
                    .map(|j| witness[j][row])
                    .collect::<Vec<_>>();
                let down = (0..self.n_columns())
                    .map(|j| witness[j][row + 1])
                    .collect::<Vec<_>>();
                let up_and_down = [up, down].concat();
                let mut constraints_checker = ConstraintChecker::<IF, EF> {
                    main: RowMajorMatrixView::new(&up_and_down, self.n_columns()),
                    constraint_index: 0,
                    errors: Vec::new(),
                    field: PhantomData,
                };
                if TypeId::of::<IF>() == TypeId::of::<EF>() {
                    unsafe {
                        self.air
                            .eval(transmute::<_, &mut ConstraintChecker<'_, EF, EF>>(
                                &mut constraints_checker,
                            ));
                    }
                } else {
                    assert_eq!(TypeId::of::<IF>(), TypeId::of::<PF<EF>>());
                    unsafe {
                        self.air
                            .eval(transmute::<_, &mut ConstraintChecker<'_, PF<EF>, EF>>(
                                &mut constraints_checker,
                            ));
                    }
                }
                handle_errors(row, &mut constraints_checker)?;
            }
        } else {
            for row in 0..witness.n_rows() {
                let up = (0..self.n_columns())
                    .map(|j| witness[j][row])
                    .collect::<Vec<_>>();
                let mut constraints_checker = ConstraintChecker {
                    main: RowMajorMatrixView::new(&up, self.n_columns()),
                    constraint_index: 0,
                    errors: Vec::new(),
                    field: PhantomData,
                };
                if TypeId::of::<IF>() == TypeId::of::<EF>() {
                    unsafe {
                        self.air
                            .eval(transmute::<_, &mut ConstraintChecker<'_, EF, EF>>(
                                &mut constraints_checker,
                            ));
                    }
                } else {
                    assert_eq!(TypeId::of::<IF>(), TypeId::of::<PF<EF>>());
                    unsafe {
                        self.air
                            .eval(transmute::<_, &mut ConstraintChecker<'_, PF<EF>, EF>>(
                                &mut constraints_checker,
                            ));
                    }
                }
                handle_errors(row, &mut constraints_checker)?;
            }
        }
        Ok(())
    }
}
