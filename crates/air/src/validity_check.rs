use multilinear_toolkit::prelude::*;
use tracing::instrument;
use utils::ConstraintChecker;

#[instrument(name = "Check trace validity", skip_all)]
pub fn check_air_validity<A: Air, EF: ExtensionField<PF<EF>>>(
    air: &A,
    extra_data: &A::ExtraData,
    columns_f: &[&[PF<EF>]],
    columns_ef: &[&[EF]],
) -> Result<(), String> {
    let n_rows = columns_f[0].len();
    assert!(columns_f.iter().all(|col| col.len() == n_rows));
    assert!(columns_ef.iter().all(|col| col.len() == n_rows));
    if columns_f.len() != air.n_columns_f_air() || columns_ef.len() != air.n_columns_ef_air() {
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
        let up_f = (0..air.n_columns_f_air())
            .map(|j| columns_f[j][row])
            .collect::<Vec<_>>();
        let up_ef = (0..air.n_columns_ef_air())
            .map(|j| columns_ef[j][row])
            .collect::<Vec<_>>();
        let down_f = air
            .down_column_indexes_f()
            .iter()
            .map(|j| columns_f[*j][row + 1])
            .collect::<Vec<_>>();
        let down_ef = air
            .down_column_indexes_ef()
            .iter()
            .map(|j| columns_ef[*j][row + 1])
            .collect::<Vec<_>>();
        let mut constraints_checker = ConstraintChecker {
            up_f,
            up_ef,
            down_f,
            down_ef,
            constraint_index: 0,
            errors: Vec::new(),
        };
        air.eval(&mut constraints_checker, extra_data);
        handle_errors(row, &constraints_checker)?;
    }
    // last transition:
    let up_f = (0..air.n_columns_f_air())
        .map(|j| columns_f[j][n_rows - 1])
        .collect::<Vec<_>>();
    let up_ef = (0..air.n_columns_ef_air())
        .map(|j| columns_ef[j][n_rows - 1])
        .collect::<Vec<_>>();
    let mut constraints_checker = ConstraintChecker {
        up_f,
        up_ef,
        down_f: air
            .down_column_indexes_f()
            .iter()
            .map(|j| columns_f[*j][n_rows - 1])
            .collect::<Vec<_>>(),
        down_ef: air
            .down_column_indexes_ef()
            .iter()
            .map(|j| columns_ef[*j][n_rows - 1])
            .collect::<Vec<_>>(),
        constraint_index: 0,
        errors: Vec::new(),
    };
    air.eval(&mut constraints_checker, extra_data);
    handle_errors(n_rows - 1, &constraints_checker)?;
    Ok(())
}
