use multilinear_toolkit::prelude::*;
use p3_air::{Air, AirBuilder, BaseAir};
use p3_koala_bear::{KoalaBear, QuinticExtensionFieldKB};
use rand::{Rng, SeedableRng, rngs::StdRng};
use utils::{build_prover_state, build_verifier_state};

use crate::{prove::prove_air, table::AirTable, verify::verify_air};

const UNIVARIATE_SKIPS: usize = 3;

const N_COLS_WITHOUT_SHIFT: usize = 2;

type F = KoalaBear;
type EF = QuinticExtensionFieldKB;

struct ExampleStructuredAir<const N_COLUMNS: usize, const N_PREPROCESSED_COLUMNS: usize>;

impl<F, const N_COLUMNS: usize, const N_PREPROCESSED_COLUMNS: usize> BaseAir<F>
    for ExampleStructuredAir<N_COLUMNS, N_PREPROCESSED_COLUMNS>
{
    fn width(&self) -> usize {
        N_COLUMNS
    }
    fn degree(&self) -> usize {
        N_PREPROCESSED_COLUMNS - N_COLS_WITHOUT_SHIFT
    }
    fn columns_with_shift(&self) -> Vec<usize> {
        [
            (0..N_PREPROCESSED_COLUMNS - N_COLS_WITHOUT_SHIFT).collect::<Vec<_>>(),
            (N_PREPROCESSED_COLUMNS..N_COLUMNS).collect::<Vec<_>>(),
        ]
        .concat()
    }
}

impl<AB: AirBuilder, const N_COLUMNS: usize, const N_PREPROCESSED_COLUMNS: usize> Air<AB>
    for ExampleStructuredAir<N_COLUMNS, N_PREPROCESSED_COLUMNS>
{
    #[inline]
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let up = main[..N_COLUMNS].to_vec();
        let down = main[N_COLUMNS..].to_vec();
        assert_eq!(down.len(), N_COLUMNS - N_COLS_WITHOUT_SHIFT);

        for j in N_PREPROCESSED_COLUMNS..N_COLUMNS {
            builder.assert_eq(
                down[j - N_COLS_WITHOUT_SHIFT].clone(),
                up[j].clone()
                    + AB::F::from_usize(j)
                    + (0..N_PREPROCESSED_COLUMNS - N_COLS_WITHOUT_SHIFT)
                        .map(|k| AB::Expr::from(down[k].clone()))
                        .product::<AB::Expr>(),
            );
        }
    }
}

fn generate_structured_trace<const N_COLUMNS: usize, const N_PREPROCESSED_COLUMNS: usize>(
    n_rows: usize,
) -> Vec<Vec<F>> {
    let mut trace = vec![];
    let mut rng = StdRng::seed_from_u64(0);
    for _ in 0..N_PREPROCESSED_COLUMNS {
        trace.push((0..n_rows).map(|_| rng.random()).collect::<Vec<F>>());
    }
    let mut witness_cols = vec![vec![F::ZERO]; N_COLUMNS - N_PREPROCESSED_COLUMNS];
    for i in 1..n_rows {
        for (j, witness_col) in witness_cols
            .iter_mut()
            .enumerate()
            .take(N_COLUMNS - N_PREPROCESSED_COLUMNS)
        {
            let witness_cols_j_i_min_1 = witness_col[i - 1];
            witness_col.push(
                witness_cols_j_i_min_1
                    + F::from_usize(j + N_PREPROCESSED_COLUMNS)
                    + (0..N_PREPROCESSED_COLUMNS - N_COLS_WITHOUT_SHIFT)
                        .map(|k| trace[k][i])
                        .product::<F>(),
            );
        }
    }
    trace.extend(witness_cols);
    trace
}

#[test]
fn test_air() {
    const N_COLUMNS: usize = 17;
    const N_PREPROCESSED_COLUMNS: usize = 5;
    const _: () = assert!(N_PREPROCESSED_COLUMNS > N_COLS_WITHOUT_SHIFT);
    let log_n_rows = 12;
    let n_rows = 1 << log_n_rows;
    let mut prover_state = build_prover_state::<EF>();

    let columns_plus_one =
        generate_structured_trace::<N_COLUMNS, N_PREPROCESSED_COLUMNS>(n_rows + 1);
    let columns_ref = columns_plus_one
        .iter()
        .map(|col| &col[..n_rows])
        .collect::<Vec<_>>();
    let mut last_row = columns_plus_one
        .iter()
        .map(|col| col[n_rows])
        .collect::<Vec<_>>();
    last_row.drain(N_PREPROCESSED_COLUMNS - N_COLS_WITHOUT_SHIFT..N_PREPROCESSED_COLUMNS);
    let last_row_ef = last_row.iter().map(|&v| EF::from(v)).collect::<Vec<_>>();

    let table = AirTable::<EF, _>::new(ExampleStructuredAir::<N_COLUMNS, N_PREPROCESSED_COLUMNS>);

    table.check_trace_validity(&columns_ref, &last_row).unwrap();

    let (point_prover, evaluations_remaining_to_prove) = prove_air(
        &mut prover_state,
        &table,
        UNIVARIATE_SKIPS,
        &columns_ref,
        &last_row,
    );
    let mut verifier_state = build_verifier_state(&prover_state);
    let (point_verifier, evaluations_remaining_to_verify) = verify_air(
        &mut verifier_state,
        &table,
        UNIVARIATE_SKIPS,
        log_n_rows,
        &last_row_ef,
    )
    .unwrap();
    assert_eq!(point_prover, point_verifier);
    assert_eq!(
        &evaluations_remaining_to_prove,
        &evaluations_remaining_to_verify
    );
    for i in 0..N_COLUMNS {
        assert_eq!(
            columns_ref[i].evaluate(&point_prover),
            evaluations_remaining_to_verify[i]
        );
    }
}
