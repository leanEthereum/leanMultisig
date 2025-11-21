use multilinear_toolkit::prelude::*;
use p3_air::{Air, AirBuilder};
use p3_koala_bear::{KoalaBear, QuinticExtensionFieldKB};
use rand::{Rng, SeedableRng, rngs::StdRng};
use utils::{build_prover_state, build_verifier_state};

use air::{check_air_validity, prove_air, verify_air};

const UNIVARIATE_SKIPS: usize = 3;

const N_COLS_F: usize = 2;

type F = KoalaBear;
type EF = QuinticExtensionFieldKB;

struct ExampleStructuredAir<
    const N_COLUMNS: usize,
    const N_PREPROCESSED_COLUMNS: usize,
    const VIRTUAL_COLUMN: bool,
>;

impl<const N_COLUMNS: usize, const N_PREPROCESSED_COLUMNS: usize, const VIRTUAL_COLUMN: bool> Air
    for ExampleStructuredAir<N_COLUMNS, N_PREPROCESSED_COLUMNS, VIRTUAL_COLUMN>
{
    type ExtraData = Vec<EF>;

    fn n_columns_f_air(&self) -> usize {
        N_COLS_F
    }
    fn n_columns_ef_air(&self) -> usize {
        N_COLUMNS - N_COLS_F
    }
    fn degree(&self) -> usize {
        N_PREPROCESSED_COLUMNS
    }
    fn n_constraints(&self) -> usize {
        50 // too much, but ok for tests
    }
    fn down_column_indexes_f(&self) -> Vec<usize> {
        vec![]
    }
    fn down_column_indexes_ef(&self) -> Vec<usize> {
        (N_PREPROCESSED_COLUMNS - N_COLS_F..N_COLUMNS - N_COLS_F).collect::<Vec<_>>()
    }

    #[inline]
    fn eval<AB: AirBuilder>(&self, builder: &mut AB, _: &Self::ExtraData) {
        let up_f = builder.up_f().to_vec();
        let up_ef = builder.up_ef().to_vec();
        let down_ef = builder.down_ef().to_vec();
        assert_eq!(up_f.len(), N_COLS_F);
        assert_eq!(up_f.len() + up_ef.len(), N_COLUMNS);
        assert_eq!(down_ef.len(), N_COLUMNS - N_PREPROCESSED_COLUMNS);

        if VIRTUAL_COLUMN {
            // virtual column A = col_0 * col_1 + col_2
            // virtual column B = col_0 - col_1
            builder.eval_virtual_column(up_ef[0].clone() + up_f[0].clone() * up_f[1].clone());
            builder.eval_virtual_column(AB::EF::from(up_f[0].clone() - up_f[1].clone()));
        }

        for j in N_PREPROCESSED_COLUMNS..N_COLUMNS {
            builder.assert_eq_ef(
                down_ef[j - N_PREPROCESSED_COLUMNS].clone(),
                up_ef[j - N_COLS_F].clone()
                    + AB::F::from_usize(j)
                    + (0..N_PREPROCESSED_COLUMNS - N_COLS_F)
                        .map(|k| up_ef[k].clone())
                        .product::<AB::EF>()
                        * up_f[0].clone()
                        * up_f[1].clone(),
            );
        }
    }
}

fn generate_trace<const N_COLUMNS: usize, const N_PREPROCESSED_COLUMNS: usize>(
    n_rows: usize,
) -> (Vec<Vec<F>>, Vec<Vec<EF>>) {
    let mut rng = StdRng::seed_from_u64(0);
    let mut trace_f = vec![];
    for _ in 0..N_COLS_F {
        trace_f.push((0..n_rows).map(|_| rng.random()).collect::<Vec<F>>());
    }
    let mut trace_ef = vec![];
    for _ in N_COLS_F..N_PREPROCESSED_COLUMNS {
        trace_ef.push((0..n_rows).map(|_| rng.random()).collect::<Vec<EF>>());
    }
    let mut witness_cols = vec![vec![EF::ZERO]; N_COLUMNS - N_PREPROCESSED_COLUMNS];
    for i in 1..n_rows {
        for (j, witness_col) in witness_cols.iter_mut().enumerate() {
            let witness_cols_j_i_min_1 = witness_col[i - 1];
            witness_col.push(
                witness_cols_j_i_min_1
                    + F::from_usize(j + N_PREPROCESSED_COLUMNS)
                    + (0..3).map(|k| trace_ef[k][i - 1]).product::<EF>()
                        * trace_f[0][i - 1]
                        * trace_f[1][i - 1],
            );
        }
    }
    trace_ef.extend(witness_cols);
    (trace_f, trace_ef)
}

#[test]
fn test_air() {
    test_air_helper::<true>();
    test_air_helper::<false>();
}

fn test_air_helper<const VIRTUAL_COLUMN: bool>() {
    const N_COLUMNS: usize = 17;
    const N_PREPROCESSED_COLUMNS: usize = 5;
    let log_n_rows = 12;
    let n_rows = 1 << log_n_rows;
    let mut prover_state = build_prover_state::<EF>();

    let (columns_plus_one_f, columns_plus_one_ef) =
        generate_trace::<N_COLUMNS, N_PREPROCESSED_COLUMNS>(n_rows + 1);
    let columns_ref_f = columns_plus_one_f
        .iter()
        .map(|col| &col[..n_rows])
        .collect::<Vec<_>>();
    let columns_ref_ef = columns_plus_one_ef
        .iter()
        .map(|col| &col[..n_rows])
        .collect::<Vec<_>>();
    let mut last_row_ef = columns_plus_one_ef
        .iter()
        .map(|col| col[n_rows])
        .collect::<Vec<_>>();
    last_row_ef = last_row_ef[N_PREPROCESSED_COLUMNS - N_COLS_F..].to_vec();

    let virtual_column_statement_prover = if VIRTUAL_COLUMN {
        let virtual_column_a = columns_ref_f[0]
            .iter()
            .zip(columns_ref_f[1].iter())
            .zip(columns_ref_ef[0].iter())
            .map(|((&a, &b), &c)| c + a * b)
            .collect::<Vec<_>>();
        let virtual_column_evaluation_point =
            MultilinearPoint(prover_state.sample_vec(log_n_rows + 1 - UNIVARIATE_SKIPS));
        let selectors = univariate_selectors::<PF<EF>>(UNIVARIATE_SKIPS);
        let virtual_column_value_a = evaluate_univariate_multilinear::<_, _, _, true>(
            &virtual_column_a,
            &virtual_column_evaluation_point,
            &selectors,
            None,
        );
        let virtual_column_b = columns_ref_f[0]
            .iter()
            .zip(columns_ref_f[1].iter())
            .map(|(&a, &b)| EF::from(a - b))
            .collect::<Vec<_>>();
        let virtual_column_value_b = evaluate_univariate_multilinear::<_, _, _, true>(
            &virtual_column_b,
            &virtual_column_evaluation_point,
            &selectors,
            None,
        );
        prover_state.add_extension_scalar(virtual_column_value_a);
        prover_state.add_extension_scalar(virtual_column_value_b);

        Some(MultiEvaluation::new(
            virtual_column_evaluation_point.0.clone(),
            vec![virtual_column_value_a, virtual_column_value_b],
        ))
    } else {
        None
    };

    let air = ExampleStructuredAir::<N_COLUMNS, N_PREPROCESSED_COLUMNS, VIRTUAL_COLUMN> {};

    check_air_validity(
        &air,
        &vec![],
        &columns_ref_f,
        &columns_ref_ef,
        &[],
        &last_row_ef,
    )
    .unwrap();

    let (point_prover, evaluations_remaining_to_prove_f, evaluations_remaining_to_prove_ef) =
        prove_air(
            &mut prover_state,
            &air,
            vec![],
            UNIVARIATE_SKIPS,
            &columns_ref_f,
            &columns_ref_ef,
            &[],
            &last_row_ef,
            virtual_column_statement_prover,
            true,
        );
    let mut verifier_state = build_verifier_state(&prover_state);

    let virtual_column_statement_verifier = if VIRTUAL_COLUMN {
        let virtual_column_evaluation_point =
            MultilinearPoint(verifier_state.sample_vec(log_n_rows + 1 - UNIVARIATE_SKIPS));
        let virtual_column_value_a = verifier_state.next_extension_scalar().unwrap();
        let virtual_column_value_b = verifier_state.next_extension_scalar().unwrap();
        Some(MultiEvaluation::new(
            virtual_column_evaluation_point.0.clone(),
            vec![virtual_column_value_a, virtual_column_value_b],
        ))
    } else {
        None
    };

    let (point_verifier, evaluations_remaining_to_verify_f, evaluations_remaining_to_verify_ef) =
        verify_air(
            &mut verifier_state,
            &air,
            vec![],
            UNIVARIATE_SKIPS,
            log_n_rows,
            &[],
            &last_row_ef,
            virtual_column_statement_verifier,
        )
        .unwrap();
    assert_eq!(point_prover, point_verifier);
    assert_eq!(
        &evaluations_remaining_to_prove_f,
        &evaluations_remaining_to_verify_f
    );
    assert_eq!(
        &evaluations_remaining_to_prove_ef,
        &evaluations_remaining_to_verify_ef
    );
    for i in 0..N_COLS_F {
        assert_eq!(
            columns_ref_f[i].evaluate(&point_prover),
            evaluations_remaining_to_verify_f[i]
        );
    }
    for i in 0..N_COLUMNS - N_COLS_F {
        assert_eq!(
            columns_ref_ef[i].evaluate(&point_prover),
            evaluations_remaining_to_verify_ef[i]
        );
    }
}
