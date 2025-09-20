use std::borrow::Borrow;

use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::PrimeCharacteristicRing;
use p3_koala_bear::{KoalaBear, QuinticExtensionFieldKB};
use p3_matrix::Matrix;
use rand::{Rng, SeedableRng, rngs::StdRng};
use utils::{build_prover_state, build_verifier_state, padd_with_zero_to_next_power_of_two};
use whir_p3::poly::evals::EvaluationsList;

use crate::{table::AirTable, witness::AirWitness};

const UNIVARIATE_SKIPS: usize = 3;

type F = KoalaBear;
type EF = QuinticExtensionFieldKB;

struct ExampleStructuredAir<const N_COLUMNS: usize, const N_PREPROCESSED_COLUMNS: usize>;

impl<F, const N_COLUMNS: usize, const N_PREPROCESSED_COLUMNS: usize> BaseAir<F>
    for ExampleStructuredAir<N_COLUMNS, N_PREPROCESSED_COLUMNS>
{
    fn width(&self) -> usize {
        N_COLUMNS
    }
    fn structured(&self) -> bool {
        true
    }
    fn degree(&self) -> usize {
        N_PREPROCESSED_COLUMNS
    }
}

impl<AB: AirBuilder, const N_COLUMNS: usize, const N_PREPROCESSED_COLUMNS: usize> Air<AB>
    for ExampleStructuredAir<N_COLUMNS, N_PREPROCESSED_COLUMNS>
{
    #[inline]
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let up = main.row_slice(0).expect("The matrix is empty?");
        let up: &[AB::Var] = (*up).borrow();
        assert_eq!(up.len(), N_COLUMNS);
        let down = main.row_slice(1).expect("The matrix is empty?");
        let down: &[AB::Var] = (*down).borrow();
        assert_eq!(down.len(), N_COLUMNS);

        for j in N_PREPROCESSED_COLUMNS..N_COLUMNS {
            builder.assert_eq(
                down[j].clone(),
                up[j].clone()
                    + AB::F::from_usize(j)
                    + (0..N_PREPROCESSED_COLUMNS)
                        .map(|k| AB::Expr::from(down[k].clone()))
                        .product::<AB::Expr>(),
            );
        }
    }
}

struct ExampleUnstructuredAir<const N_COLUMNS: usize, const N_PREPROCESSED_COLUMNS: usize>;

impl<F, const N_COLUMNS: usize, const N_PREPROCESSED_COLUMNS: usize> BaseAir<F>
    for ExampleUnstructuredAir<N_COLUMNS, N_PREPROCESSED_COLUMNS>
{
    fn width(&self) -> usize {
        N_COLUMNS
    }
    fn structured(&self) -> bool {
        false
    }
    fn degree(&self) -> usize {
        N_PREPROCESSED_COLUMNS
    }
}

impl<AB: AirBuilder, const N_COLUMNS: usize, const N_PREPROCESSED_COLUMNS: usize> Air<AB>
    for ExampleUnstructuredAir<N_COLUMNS, N_PREPROCESSED_COLUMNS>
{
    #[inline]
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let up = main.row_slice(0).expect("The matrix is empty?");
        let up: &[AB::Var] = (*up).borrow();
        assert_eq!(up.len(), N_COLUMNS);

        for j in N_PREPROCESSED_COLUMNS..N_COLUMNS {
            builder.assert_eq(
                up[j].clone(),
                (0..N_PREPROCESSED_COLUMNS)
                    .map(|k| AB::Expr::from(up[k].clone()))
                    .product::<AB::Expr>()
                    + AB::F::from_usize(j),
            );
        }
    }
}

fn generate_structured_trace<const N_COLUMNS: usize, const N_PREPROCESSED_COLUMNS: usize>(
    log_length: usize,
) -> Vec<Vec<F>> {
    let n_rows = 1 << log_length;
    let mut trace = vec![];
    let mut rng = StdRng::seed_from_u64(0);
    for _ in 0..N_PREPROCESSED_COLUMNS {
        trace.push((0..n_rows).map(|_| rng.random()).collect::<Vec<F>>());
    }
    let mut witness_cols = vec![vec![F::ZERO]; N_COLUMNS - N_PREPROCESSED_COLUMNS];
    let mut prev_values = vec![F::ZERO; N_COLUMNS - N_PREPROCESSED_COLUMNS];
    let mut column_iters = trace[..N_PREPROCESSED_COLUMNS]
        .iter()
        .map(|col| col.iter())
        .collect::<Vec<_>>();
    if column_iters.is_empty() {
        trace.extend(witness_cols);
        return trace;
    }
    for iter in &mut column_iters {
        iter.next(); // skip first row, already initialised
    }
    loop {
        let mut row_product = F::ONE;
        let mut progressed = true;
        for iter in &mut column_iters {
            match iter.next() {
                Some(value) => row_product *= *value,
                None => {
                    progressed = false;
                    break;
                }
            }
        }
        if !progressed {
            break;
        }
        for (j, (witness_col, prev)) in witness_cols
            .iter_mut()
            .zip(prev_values.iter_mut())
            .enumerate()
        {
            let next_val = *prev + F::from_usize(j + N_PREPROCESSED_COLUMNS) + row_product;
            witness_col.push(next_val);
            *prev = next_val;
        }
    }
    trace.extend(witness_cols);
    trace
}

fn generate_unstructured_trace<const N_COLUMNS: usize, const N_PREPROCESSED_COLUMNS: usize>(
    log_length: usize,
) -> Vec<Vec<F>> {
    let n_rows = 1 << log_length;
    let mut trace = vec![];
    let mut rng = StdRng::seed_from_u64(0);
    for _ in 0..N_PREPROCESSED_COLUMNS {
        trace.push((0..n_rows).map(|_| rng.random()).collect::<Vec<F>>());
    }
    let mut witness_cols = vec![vec![]; N_COLUMNS - N_PREPROCESSED_COLUMNS];
    let mut column_iters = trace[..N_PREPROCESSED_COLUMNS]
        .iter()
        .map(|col| col.iter())
        .collect::<Vec<_>>();
    if column_iters.is_empty() {
        trace.extend(witness_cols);
        return trace;
    }
    loop {
        let mut row_product = F::ONE;
        let mut progressed = true;
        for iter in &mut column_iters {
            match iter.next() {
                Some(value) => row_product *= *value,
                None => {
                    progressed = false;
                    break;
                }
            }
        }
        if !progressed {
            break;
        }
        for (j, witness_col) in witness_cols.iter_mut().enumerate() {
            witness_col.push(F::from_usize(j + N_PREPROCESSED_COLUMNS) + row_product);
        }
    }
    trace.extend(witness_cols);
    trace
}

#[test]
fn test_structured_air() {
    const N_COLUMNS: usize = 17;
    const N_PREPROCESSED_COLUMNS: usize = 3;
    let log_n_rows = 12;
    let mut prover_state = build_prover_state::<EF>();

    let columns = generate_structured_trace::<N_COLUMNS, N_PREPROCESSED_COLUMNS>(log_n_rows);
    let column_groups = vec![0..N_PREPROCESSED_COLUMNS, N_PREPROCESSED_COLUMNS..N_COLUMNS];
    let witness = AirWitness::new(&columns, &column_groups);

    let table = AirTable::<EF, _, _>::new(
        ExampleStructuredAir::<N_COLUMNS, N_PREPROCESSED_COLUMNS>,
        ExampleStructuredAir::<N_COLUMNS, N_PREPROCESSED_COLUMNS>,
    );
    table.check_trace_validity(&witness).unwrap();
    let evaluations_remaining_to_prove =
        table.prove_base(&mut prover_state, UNIVARIATE_SKIPS, witness);
    let mut verifier_state = build_verifier_state(&prover_state);
    let evaluations_remaining_to_verify = table
        .verify(
            &mut verifier_state,
            UNIVARIATE_SKIPS,
            log_n_rows,
            &column_groups,
        )
        .unwrap();
    assert_eq!(
        &evaluations_remaining_to_prove,
        &evaluations_remaining_to_verify
    );
    assert_eq!(
        padd_with_zero_to_next_power_of_two(&columns[..N_PREPROCESSED_COLUMNS].concat())
            .evaluate(&evaluations_remaining_to_verify[0].point),
        evaluations_remaining_to_verify[0].value
    );
    assert_eq!(
        padd_with_zero_to_next_power_of_two(&columns[N_PREPROCESSED_COLUMNS..N_COLUMNS].concat())
            .evaluate(&evaluations_remaining_to_verify[1].point),
        evaluations_remaining_to_verify[1].value
    );
}

#[test]
fn test_unstructured_air() {
    const N_COLUMNS: usize = 18;
    const N_PREPROCESSED_COLUMNS: usize = 5;
    let log_n_rows = 12;
    let mut prover_state = build_prover_state::<EF>();

    let columns = generate_unstructured_trace::<N_COLUMNS, N_PREPROCESSED_COLUMNS>(log_n_rows);
    let column_groups = vec![0..N_PREPROCESSED_COLUMNS, N_PREPROCESSED_COLUMNS..N_COLUMNS];
    let witness = AirWitness::new(&columns, &column_groups);

    let table = AirTable::<EF, _, _>::new(
        ExampleUnstructuredAir::<N_COLUMNS, N_PREPROCESSED_COLUMNS>,
        ExampleUnstructuredAir::<N_COLUMNS, N_PREPROCESSED_COLUMNS>,
    );
    table.check_trace_validity(&witness).unwrap();
    let evaluations_remaining_to_prove =
        table.prove_base(&mut prover_state, UNIVARIATE_SKIPS, witness);
    let mut verifier_state = build_verifier_state(&prover_state);
    let evaluations_remaining_to_verify = table
        .verify(
            &mut verifier_state,
            UNIVARIATE_SKIPS,
            log_n_rows,
            &column_groups,
        )
        .unwrap();
    assert_eq!(
        &evaluations_remaining_to_prove,
        &evaluations_remaining_to_verify
    );
    assert_eq!(
        padd_with_zero_to_next_power_of_two(&columns[..N_PREPROCESSED_COLUMNS].concat())
            .evaluate(&evaluations_remaining_to_verify[0].point),
        evaluations_remaining_to_verify[0].value
    );
    assert_eq!(
        padd_with_zero_to_next_power_of_two(&columns[N_PREPROCESSED_COLUMNS..N_COLUMNS].concat())
            .evaluate(&evaluations_remaining_to_verify[1].point),
        evaluations_remaining_to_verify[1].value
    );
}
