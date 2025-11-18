use multilinear_toolkit::prelude::*;
use p3_air::Air;
use tracing::instrument;
use utils::ConstraintChecker;

#[derive(Debug)]
pub struct AirTable<EF: Field, A> {
    pub air: A,
    _phantom: std::marker::PhantomData<EF>,
}

impl<EF: ExtensionField<PF<EF>>, A: Air> AirTable<EF, A> {
    pub fn new(air: A) -> Self {
        Self {
            air,
            _phantom: std::marker::PhantomData,
        }
    }

    pub fn n_columns(&self) -> usize {
        A::n_columns()
    }

    pub fn n_constraints(&self) -> usize {
        A::n_constraints()
    }

    pub fn down_column_indexes(&self) -> Vec<usize> {
        A::down_column_indexes()
    }

    #[instrument(name = "Check trace validity", skip_all)]
    pub fn check_trace_validity(
        &self,
        columns_f: &[&[PF<EF>]],
        columns_ef: &[&[EF]],
        last_row: &[EF],
    ) -> Result<(), String> {
        let n_rows = columns_f[0].len();
        assert!(columns_f.iter().all(|col| col.len() == n_rows));
        assert!(columns_ef.iter().all(|col| col.len() == n_rows));
        if columns_f.len() + columns_ef.len() != self.n_columns() {
            return Err("Invalid number of columns".to_string());
        }
        let handle_errors = |row: usize, constraint_checker: &ConstraintChecker<EF>| {
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
            let up_f = (0..A::n_columns_f())
                .map(|j| columns_f[j][row])
                .collect::<Vec<_>>();
            let up_ef = (0..A::n_columns_ef())
                .map(|j| columns_ef[j][row])
                .collect::<Vec<_>>();
            let down_f = self
                .down_column_indexes()
                .iter()
                .filter(|i| **i < A::n_columns_f())
                .map(|j| columns_f[*j][row + 1])
                .collect::<Vec<_>>();
            let down_ef = self
                .down_column_indexes()
                .iter()
                .filter(|i| **i >= A::n_columns_f())
                .map(|j| columns_ef[*j - A::n_columns_f()][row + 1])
                .collect::<Vec<_>>();
            let mut constraints_checker = ConstraintChecker {
                up_f,
                up_ef,
                down_f,
                down_ef,
                constraint_index: 0,
                errors: Vec::new(),
            };
            self.air.eval(&mut constraints_checker);
            handle_errors(row, &constraints_checker)?;
        }
        // last transition:
        let up_f = (0..A::n_columns_f())
            .map(|j| columns_f[j][n_rows - 1])
            .collect::<Vec<_>>();
        let up_ef = (0..A::n_columns_ef())
            .map(|j| columns_ef[j][n_rows - 1])
            .collect::<Vec<_>>();
        let last_row_f_count = self
            .down_column_indexes()
            .iter()
            .filter(|i| **i < A::n_columns_f())
            .count();
        let last_row_f = last_row[..last_row_f_count]
            .iter()
            .map(|e| e.as_base().unwrap())
            .collect::<Vec<_>>();
        let last_row_ef = last_row[last_row_f_count..].to_vec();
        let mut constraints_checker = ConstraintChecker {
            up_f,
            up_ef,
            down_f: last_row_f,
            down_ef: last_row_ef,
            constraint_index: 0,
            errors: Vec::new(),
        };
        self.air.eval(&mut constraints_checker);
        handle_errors(n_rows - 1, &constraints_checker)?;
        Ok(())
    }
}
