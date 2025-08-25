use std::{any::TypeId, marker::PhantomData, mem::transmute};

use p3_field::{ExtensionField, Field};
use p3_matrix::dense::RowMajorMatrixView;
use p3_uni_stark::get_symbolic_constraints;
use utils::{ConstraintChecker, PF};

use crate::{MyAir, witness::AirWitness};

#[derive(Debug)]
pub struct AirTable<EF: Field, A> {
    pub air: A,
    pub n_constraints: usize,
    _phantom: PhantomData<EF>,
}

impl<EF: ExtensionField<PF<EF>>, A: MyAir<EF>> AirTable<EF, A> {
    pub fn new(air: A) -> Self {
        let symbolic_constraints = get_symbolic_constraints(&air, 0, 0);
        let n_constraints = symbolic_constraints.len();
        let constraint_degree = symbolic_constraints
            .iter()
            .map(p3_uni_stark::SymbolicExpression::degree_multiple)
            .max()
            .unwrap();
        assert_eq!(constraint_degree, air.degree());
        Self {
            air,
            n_constraints,
            _phantom: PhantomData,
        }
    }

    pub fn n_columns(&self) -> usize {
        self.air.width()
    }

    pub fn check_trace_validity<IF: ExtensionField<PF<EF>>>(
        &self,
        witness: &AirWitness<'_, IF>,
    ) -> Result<(), String>
    where
        A: MyAir<EF>,
        EF: ExtensionField<IF>,
    {
        let width = self.air.width();
        let rows = witness.n_rows();

        if witness.n_columns() != width {
            return Err("Invalid number of columns".to_string());
        }

        // Erased-type dispatch to the concrete ConstraintChecker expected by `air.eval`.
        let eval_erased = |checker: &mut ConstraintChecker<'_, IF, EF>| unsafe {
            if TypeId::of::<IF>() == TypeId::of::<EF>() {
                self.air
                    .eval(transmute::<_, &mut ConstraintChecker<'_, EF, EF>>(checker));
            } else {
                assert_eq!(TypeId::of::<IF>(), TypeId::of::<PF<EF>>());
                self.air
                    .eval(transmute::<_, &mut ConstraintChecker<'_, PF<EF>, EF>>(
                        checker,
                    ));
            }
        };

        // Common per-row runner.
        let run_row = |row: usize, slice: Vec<IF>| -> Result<(), String> {
            let mut checker = ConstraintChecker {
                main: RowMajorMatrixView::new(&slice, width),
                constraint_index: 0,
                errors: Vec::new(),
                field: PhantomData,
            };

            eval_erased(&mut checker);

            if !checker.errors.is_empty() {
                return Err(format!(
                    "Trace is not valid at row {}: contraints not respected: {}",
                    row,
                    checker
                        .errors
                        .iter()
                        .map(std::string::ToString::to_string)
                        .collect::<Vec<_>>()
                        .join(", ")
                ));
            }
            Ok(())
        };

        if self.air.structured() {
            // same semantics as original: panics if rows == 0 due to `rows - 1`
            for row in 0..rows - 1 {
                let mut up_and_down = Vec::with_capacity(width * 2);
                up_and_down.extend((0..width).map(|j| witness[j][row]));
                up_and_down.extend((0..width).map(|j| witness[j][row + 1]));
                run_row(row, up_and_down)?;
            }
        } else {
            for row in 0..rows {
                let up = (0..width).map(|j| witness[j][row]).collect();
                run_row(row, up)?;
            }
        }

        Ok(())
    }
}
