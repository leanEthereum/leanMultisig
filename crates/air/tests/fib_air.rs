use multilinear_toolkit::prelude::*;
use p3_koala_bear::{KoalaBear, QuinticExtensionFieldKB};
use utils::{build_prover_state, build_verifier_state};

use air::{check_air_validity, prove_air, verify_air};

const UNIVARIATE_SKIPS: usize = 3;

type F = KoalaBear;
type EF = QuinticExtensionFieldKB;

struct FibonacciAir;

impl Air for FibonacciAir {
    type ExtraData = Vec<EF>;

    fn n_columns_f_air(&self) -> usize {
        1
    }
    fn n_columns_ef_air(&self) -> usize {
        1
    }
    fn degree_air(&self) -> usize {
        1
    }
    fn n_constraints(&self) -> usize {
        10 // too much, but ok for tests
    }
    fn down_column_indexes_f(&self) -> Vec<usize> {
        vec![0]
    }
    fn down_column_indexes_ef(&self) -> Vec<usize> {
        vec![0]
    }
    #[inline]
    fn eval<AB: AirBuilder>(&self, builder: &mut AB, _: &Self::ExtraData) {
        let a_up = builder.up_f()[0].clone();
        let b_up = builder.up_ef()[0].clone();
        let a_down = builder.down_f()[0].clone();
        let b_down = builder.down_ef()[0].clone();
        builder.assert_eq_ef(b_down, b_up.clone() + a_up);
        builder.assert_eq_ef(AB::EF::from(a_down), b_up);
    }
}

fn generate_trace(n_rows: usize) -> (Vec<F>, Vec<EF>) {
    let mut col_a = vec![F::ONE];
    let mut col_b = vec![EF::ONE];
    for i in 1..n_rows {
        let a_next = col_b[i - 1].as_base().unwrap();
        let b_next = col_b[i - 1] + col_a[i - 1];
        col_a.push(a_next);
        col_b.push(b_next);
    }
    (col_a, col_b)
}

#[test]
fn test_air_fibonacci() {
    let log_n_rows = 14;
    let n_rows = 1 << log_n_rows;
    let mut prover_state = build_prover_state();

    let (columns_plus_one_f, columns_plus_one_ef) = generate_trace(n_rows + 1);
    let columns_ref_f = vec![&columns_plus_one_f[..n_rows]];
    let columns_ref_ef = vec![&columns_plus_one_ef[..n_rows]];
    let last_row_f = vec![columns_plus_one_f[n_rows]];
    let last_row_ef = vec![columns_plus_one_ef[n_rows]];

    let air = FibonacciAir {};

    check_air_validity(
        &air,
        &vec![],
        &columns_ref_f,
        &columns_ref_ef,
        &last_row_f,
        &last_row_ef,
    )
    .unwrap();

    let (point_prover, evaluations_remaining_to_prove_f, evaluations_remaining_to_prove_ef) = prove_air(
        &mut prover_state,
        &air,
        vec![],
        UNIVARIATE_SKIPS,
        &columns_ref_f,
        &columns_ref_ef,
        &last_row_f,
        &last_row_ef,
        None,
        true,
    );
    let mut verifier_state = build_verifier_state(prover_state);

    let (point_verifier, evaluations_remaining_to_verify_f, evaluations_remaining_to_verify_ef) = verify_air(
        &mut verifier_state,
        &air,
        vec![],
        UNIVARIATE_SKIPS,
        log_n_rows,
        &last_row_f,
        &last_row_ef,
        None,
    )
    .unwrap();
    assert_eq!(point_prover, point_verifier);
    assert_eq!(&evaluations_remaining_to_prove_f, &evaluations_remaining_to_verify_f);
    assert_eq!(&evaluations_remaining_to_prove_ef, &evaluations_remaining_to_verify_ef);
    assert_eq!(
        columns_ref_f[0].evaluate(&point_prover),
        evaluations_remaining_to_verify_f[0]
    );
    assert_eq!(
        columns_ref_ef[0].evaluate(&point_prover),
        evaluations_remaining_to_verify_ef[0]
    );
}
