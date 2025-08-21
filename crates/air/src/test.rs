use std::borrow::Borrow;

use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::PrimeCharacteristicRing;
use p3_field::extension::BinomialExtensionField;
use p3_koala_bear::KoalaBear;
use p3_matrix::Matrix;
use rand::{Rng, SeedableRng, rngs::StdRng};
use utils::{build_prover_state, build_verifier_state, padd_with_zero_to_next_power_of_two};
use whir_p3::poly::evals::EvaluationsList;

use crate::{prove_many_air_2, table::AirTable, verify_many_air_2, witness::AirWitness};

const UNIVARIATE_SKIPS: usize = 3;

type F = KoalaBear;
type EF = BinomialExtensionField<F, 8>;

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
                    + AB::I::from_usize(j)
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
                    + AB::I::from_usize(j),
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
    for i in 1..n_rows {
        for j in 0..N_COLUMNS - N_PREPROCESSED_COLUMNS {
            let witness_cols_j_i_min_1 = witness_cols[j][i - 1];
            witness_cols[j].push(
                witness_cols_j_i_min_1
                    + F::from_usize(j + N_PREPROCESSED_COLUMNS)
                    + (0..N_PREPROCESSED_COLUMNS)
                        .map(|k| trace[k][i])
                        .product::<F>(),
            );
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
    for i in 0..n_rows {
        for j in 0..N_COLUMNS - N_PREPROCESSED_COLUMNS {
            witness_cols[j].push(
                F::from_usize(j + N_PREPROCESSED_COLUMNS)
                    + (0..N_PREPROCESSED_COLUMNS)
                        .map(|k| trace[k][i])
                        .product::<F>(),
            );
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

    let table = AirTable::<EF, _>::new(ExampleStructuredAir::<N_COLUMNS, N_PREPROCESSED_COLUMNS>);
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

    let table = AirTable::<EF, _>::new(ExampleUnstructuredAir::<N_COLUMNS, N_PREPROCESSED_COLUMNS>);
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
fn test_many_unstructured_air() {
    const N_COLUMNS_A: usize = 10;
    const N_PREPROCESSED_COLUMNS_A: usize = 3;
    const N_COLUMNS_B: usize = 20;
    const N_PREPROCESSED_COLUMNS_B: usize = 5;
    let log_n_rows_a = vec![10, 11];
    let log_n_rows_b = vec![9, 13, 8];
    let mut prover_state = build_prover_state::<EF>();

    let tables_a = log_n_rows_a
        .iter()
        .map(|_| {
            AirTable::<EF, _>::new(ExampleUnstructuredAir::<N_COLUMNS_A, N_PREPROCESSED_COLUMNS_A>)
        })
        .collect::<Vec<_>>();
    let tables_b = log_n_rows_b
        .iter()
        .map(|_| {
            AirTable::<EF, _>::new(ExampleUnstructuredAir::<N_COLUMNS_B, N_PREPROCESSED_COLUMNS_B>)
        })
        .collect::<Vec<_>>();
    let tables_a = tables_a.iter().collect::<Vec<_>>();
    let tables_b = tables_b.iter().collect::<Vec<_>>();

    let mut traces = vec![];
    let mut column_groups = vec![];
    let column_group_a = vec![
        0..N_PREPROCESSED_COLUMNS_A,
        N_PREPROCESSED_COLUMNS_A..N_COLUMNS_A,
    ];
    let column_group_b = vec![
        0..N_PREPROCESSED_COLUMNS_B,
        N_PREPROCESSED_COLUMNS_B..N_COLUMNS_B,
    ];
    for log_n_rows in &log_n_rows_a {
        column_groups.push(column_group_a.clone());
        traces.push(generate_unstructured_trace::<
            N_COLUMNS_A,
            N_PREPROCESSED_COLUMNS_A,
        >(*log_n_rows));
    }

    for log_n_rows in &log_n_rows_b {
        column_groups.push(column_group_b.clone());
        traces.push(generate_unstructured_trace::<
            N_COLUMNS_B,
            N_PREPROCESSED_COLUMNS_B,
        >(*log_n_rows));
    }
    let mut witnesses_a = vec![];
    for trace in &traces[..log_n_rows_a.len()] {
        witnesses_a.push(AirWitness::new(trace, &column_group_a));
    }
    let mut witnesses_b = vec![];
    for trace in &traces[log_n_rows_a.len()..] {
        witnesses_b.push(AirWitness::new(trace, &column_group_b));
    }

    for (table, witness) in tables_a.iter().zip(witnesses_a.iter()) {
        table.check_trace_validity(witness).unwrap();
    }
    for (table, witness) in tables_b.iter().zip(witnesses_b.iter()) {
        table.check_trace_validity(witness).unwrap();
    }

    let evaluations_remaining_to_prove = prove_many_air_2(
        &mut prover_state,
        UNIVARIATE_SKIPS,
        &tables_a,
        &tables_b,
        &witnesses_a,
        &witnesses_b,
    );
    let mut verifier_state = build_verifier_state(&prover_state);
    let evaluations_remaining_to_verify = verify_many_air_2(
        &mut verifier_state,
        &tables_a,
        &tables_b,
        UNIVARIATE_SKIPS,
        &[log_n_rows_a, log_n_rows_b].concat(),
        &column_groups,
    )
    .unwrap();
    assert_eq!(
        &evaluations_remaining_to_prove,
        &evaluations_remaining_to_verify
    );
    for i in 0..tables_a.len() {
        assert_eq!(evaluations_remaining_to_verify[i].len(), 2);
        assert_eq!(
            padd_with_zero_to_next_power_of_two(&traces[i][..N_PREPROCESSED_COLUMNS_A].concat())
                .evaluate(&evaluations_remaining_to_verify[i][0].point),
            evaluations_remaining_to_verify[i][0].value
        );
        assert_eq!(
            padd_with_zero_to_next_power_of_two(
                &traces[i][N_PREPROCESSED_COLUMNS_A..N_COLUMNS_A].concat()
            )
            .evaluate(&evaluations_remaining_to_verify[i][1].point),
            evaluations_remaining_to_verify[i][1].value
        );
    }
    for i in tables_a.len()..tables_a.len() + tables_b.len() {
        assert_eq!(evaluations_remaining_to_verify[i].len(), 2);
        assert_eq!(
            padd_with_zero_to_next_power_of_two(&traces[i][..N_PREPROCESSED_COLUMNS_B].concat())
                .evaluate(&evaluations_remaining_to_verify[i][0].point),
            evaluations_remaining_to_verify[i][0].value
        );
        assert_eq!(
            padd_with_zero_to_next_power_of_two(
                &traces[i][N_PREPROCESSED_COLUMNS_B..N_COLUMNS_B].concat()
            )
            .evaluate(&evaluations_remaining_to_verify[i][1].point),
            evaluations_remaining_to_verify[i][1].value
        );
    }
}

#[test]
fn test_many_structured_air() {
    const N_COLUMNS_A: usize = 10;
    const N_PREPROCESSED_COLUMNS_A: usize = 3;
    const N_COLUMNS_B: usize = 20;
    const N_PREPROCESSED_COLUMNS_B: usize = 5;
    let log_n_rows_a = vec![10, 11];
    let log_n_rows_b = vec![9, 13, 8];
    let mut prover_state = build_prover_state::<EF>();

    let tables_a = log_n_rows_a
        .iter()
        .map(|_| {
            AirTable::<EF, _>::new(ExampleStructuredAir::<N_COLUMNS_A, N_PREPROCESSED_COLUMNS_A>)
        })
        .collect::<Vec<_>>();
    let tables_b = log_n_rows_b
        .iter()
        .map(|_| {
            AirTable::<EF, _>::new(ExampleStructuredAir::<N_COLUMNS_B, N_PREPROCESSED_COLUMNS_B>)
        })
        .collect::<Vec<_>>();
    let tables_a = tables_a.iter().collect::<Vec<_>>();
    let tables_b = tables_b.iter().collect::<Vec<_>>();

    let mut traces = vec![];
    let mut column_groups = vec![];
    let column_group_a = vec![
        0..N_PREPROCESSED_COLUMNS_A,
        N_PREPROCESSED_COLUMNS_A..N_COLUMNS_A,
    ];
    let column_group_b = vec![
        0..N_PREPROCESSED_COLUMNS_B,
        N_PREPROCESSED_COLUMNS_B..N_COLUMNS_B,
    ];
    for log_n_rows in &log_n_rows_a {
        column_groups.push(column_group_a.clone());
        traces.push(generate_structured_trace::<
            N_COLUMNS_A,
            N_PREPROCESSED_COLUMNS_A,
        >(*log_n_rows));
    }

    for log_n_rows in &log_n_rows_b {
        column_groups.push(column_group_b.clone());
        traces.push(generate_structured_trace::<
            N_COLUMNS_B,
            N_PREPROCESSED_COLUMNS_B,
        >(*log_n_rows));
    }
    let mut witnesses_a = vec![];
    for trace in &traces[..log_n_rows_a.len()] {
        witnesses_a.push(AirWitness::new(trace, &column_group_a));
    }
    let mut witnesses_b = vec![];
    for trace in &traces[log_n_rows_a.len()..] {
        witnesses_b.push(AirWitness::new(trace, &column_group_b));
    }

    for (table, witness) in tables_a.iter().zip(witnesses_a.iter()) {
        table.check_trace_validity(witness).unwrap();
    }
    for (table, witness) in tables_b.iter().zip(witnesses_b.iter()) {
        table.check_trace_validity(witness).unwrap();
    }

    let evaluations_remaining_to_prove = prove_many_air_2(
        &mut prover_state,
        UNIVARIATE_SKIPS,
        &tables_a,
        &tables_b,
        &witnesses_a,
        &witnesses_b,
    );
    let mut verifier_state = build_verifier_state(&prover_state);
    let evaluations_remaining_to_verify = verify_many_air_2(
        &mut verifier_state,
        &tables_a,
        &tables_b,
        UNIVARIATE_SKIPS,
        &[log_n_rows_a, log_n_rows_b].concat(),
        &column_groups,
    )
    .unwrap();
    assert_eq!(
        &evaluations_remaining_to_prove,
        &evaluations_remaining_to_verify
    );
    for i in 0..tables_a.len() {
        assert_eq!(evaluations_remaining_to_verify[i].len(), 2);
        assert_eq!(
            padd_with_zero_to_next_power_of_two(&traces[i][..N_PREPROCESSED_COLUMNS_A].concat())
                .evaluate(&evaluations_remaining_to_verify[i][0].point),
            evaluations_remaining_to_verify[i][0].value
        );
        assert_eq!(
            padd_with_zero_to_next_power_of_two(
                &traces[i][N_PREPROCESSED_COLUMNS_A..N_COLUMNS_A].concat()
            )
            .evaluate(&evaluations_remaining_to_verify[i][1].point),
            evaluations_remaining_to_verify[i][1].value
        );
    }
    for i in tables_a.len()..tables_a.len() + tables_b.len() {
        assert_eq!(evaluations_remaining_to_verify[i].len(), 2);
        assert_eq!(
            padd_with_zero_to_next_power_of_two(&traces[i][..N_PREPROCESSED_COLUMNS_B].concat())
                .evaluate(&evaluations_remaining_to_verify[i][0].point),
            evaluations_remaining_to_verify[i][0].value
        );
        assert_eq!(
            padd_with_zero_to_next_power_of_two(
                &traces[i][N_PREPROCESSED_COLUMNS_B..N_COLUMNS_B].concat()
            )
            .evaluate(&evaluations_remaining_to_verify[i][1].point),
            evaluations_remaining_to_verify[i][1].value
        );
    }
}
