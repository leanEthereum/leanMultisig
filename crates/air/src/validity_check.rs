use backend::*;
use tracing::instrument;

#[derive(Debug)]
pub struct ConstraintChecker<EF: ExtensionField<PF<EF>>> {
    pub up: Vec<PF<EF>>,
    pub down: Vec<PF<EF>>,
    pub constraint_index: usize,
    pub errors: Vec<usize>,
}

impl<EF: ExtensionField<PF<EF>>> AirBuilder for ConstraintChecker<EF> {
    type F = PF<EF>;
    type EF = EF;

    #[inline]
    fn up(&self) -> &[Self::F] {
        &self.up
    }

    #[inline]
    fn down(&self) -> &[Self::F] {
        &self.down
    }

    #[inline]
    fn assert_zero(&mut self, x: Self::F) {
        if !x.is_zero() {
            self.errors.push(self.constraint_index);
        }
        self.constraint_index += 1;
    }

    #[inline]
    fn assert_zero_ef(&mut self, x: Self::EF) {
        if !x.is_zero() {
            self.errors.push(self.constraint_index);
        }
        self.constraint_index += 1;
    }

    fn eval_virtual_column(&mut self, _: Self::EF) {
        // do nothing
    }
}

#[instrument(name = "Check trace validity", skip_all)]
pub fn check_air_validity<A: Air, EF: ExtensionField<PF<EF>>>(
    air: &A,
    extra_data: &A::ExtraData,
    columns: &[&[PF<EF>]],
) -> Result<(), String> {
    let n_rows = columns[0].len();
    assert!(columns.iter().all(|col| col.len() == n_rows));
    if columns.len() != air.n_columns() {
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
        let up = (0..air.n_columns()).map(|j| columns[j][row]).collect::<Vec<_>>();
        let down = air
            .down_column_indexes()
            .iter()
            .map(|j| columns[*j][row + 1])
            .collect::<Vec<_>>();
        let mut constraints_checker = ConstraintChecker {
            up,
            down,
            constraint_index: 0,
            errors: Vec::new(),
        };
        air.eval(&mut constraints_checker, extra_data);
        handle_errors(row, &constraints_checker)?;
    }
    // last transition:
    let up = (0..air.n_columns()).map(|j| columns[j][n_rows - 1]).collect::<Vec<_>>();
    let mut constraints_checker = ConstraintChecker {
        up,
        down: air
            .down_column_indexes()
            .iter()
            .map(|j| columns[*j][n_rows - 1])
            .collect::<Vec<_>>(),
        constraint_index: 0,
        errors: Vec::new(),
    };
    air.eval(&mut constraints_checker, extra_data);
    handle_errors(n_rows - 1, &constraints_checker)?;
    Ok(())
}
