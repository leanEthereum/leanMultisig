use multilinear_toolkit::prelude::{Evaluation, EvaluationsList, MultilinearPoint};
use p3_field::PrimeCharacteristicRing;
use p3_koala_bear::{KoalaBear, QuinticExtensionFieldKB};
use p3_util::log2_ceil_usize;
use packed_pcs::{ColDims, packed_pcs_global_statements_for_prover};
use rand::{Rng, SeedableRng, rngs::StdRng};
use utils::build_prover_state;

type F = KoalaBear;
type EF = QuinticExtensionFieldKB;
const DIM: usize = 5;
const LOG_SMALLEST_DECOMPOSITION_CHUNK: usize = 5;

#[test]
fn test_packed_lookup() {
    let n_lookups_for_execution = 3;
    let n_cycles = 7541;
    let log_n_cycles = log2_ceil_usize(n_cycles);
    let memory_size: usize = 37412;
    let n_dot_product_rows: usize = 1574;
    let log_n_dot_product_rows = log2_ceil_usize(n_dot_product_rows);
    let n_extension_field_lookups = 3;

    let mut rng = StdRng::seed_from_u64(0);
    let mut memory = F::zero_vec(memory_size.next_power_of_two());
    for i in 0..memory_size {
        memory[i] = rng.random();
    }

    let mut execution_table_indexes =
        vec![vec![0; n_cycles.next_power_of_two()]; n_lookups_for_execution];
    for cycle in 0..n_cycles {
        for lookup in 0..n_lookups_for_execution {
            execution_table_indexes[lookup][cycle] = rng.random_range(0..memory_size);
        }
    }

    let mut execution_table_values =
        vec![vec![F::ZERO; n_cycles.next_power_of_two()]; n_lookups_for_execution];
    for cycle in 0..n_cycles {
        for lookup in 0..n_lookups_for_execution {
            let index = execution_table_indexes[lookup][cycle];
            execution_table_values[lookup][cycle] = memory[index];
        }
    }

    let mut dot_product_indexes =
        vec![vec![0; n_dot_product_rows.next_power_of_two()]; n_extension_field_lookups];
    for row in 0..n_dot_product_rows {
        for lookup in 0..n_extension_field_lookups {
            dot_product_indexes[lookup][row] = rng.random_range(0..memory_size - DIM);
        }
    }

    let mut dot_product_values = vec![
        vec![F::zero_vec(n_dot_product_rows.next_power_of_two()); DIM];
        n_extension_field_lookups
    ];
    for row in 0..n_dot_product_rows {
        for lookup in 0..n_extension_field_lookups {
            let index = dot_product_indexes[lookup][row];
            for d in 0..DIM {
                dot_product_values[lookup][d][row] = memory[index + d];
            }
        }
    }

    let exec_point = MultilinearPoint((0..log_n_cycles).map(|_| rng.random()).collect::<Vec<EF>>());
    let dp_point = MultilinearPoint(
        (0..log_n_dot_product_rows)
            .map(|_| rng.random())
            .collect::<Vec<EF>>(),
    );

    let exec_values = execution_table_values
        .iter()
        .map(|col| col.evaluate(&exec_point))
        .collect::<Vec<_>>();

    let dp_values = dot_product_values
        .iter()
        .map(|cols| {
            cols.iter()
                .map(|col| col.evaluate(&dp_point))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();

    let exec_dims = vec![ColDims::padded(n_cycles, F::ZERO); n_lookups_for_execution];
    let dp_dims = vec![ColDims::padded(n_dot_product_rows, F::ZERO); DIM * n_extension_field_lookups];

    let all_dims = [exec_dims, dp_dims].concat();

    let all_colums_ref = [
        execution_table_values
            .iter()
            .map(|col| col.as_slice())
            .collect::<Vec<&[F]>>(),
        dot_product_values
            .iter()
            .flat_map(|cols| cols.iter().map(|col| col.as_slice()))
            .collect::<Vec<&[F]>>(),
    ]
    .concat();
    let (packed_polynomial, chunks) = packed_pcs::group_multilinear_claims(
        &all_colums_ref,
        &all_dims,
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
    );

    let mut initial_statements = exec_values
        .iter()
        .map(|&v| vec![Evaluation::new(exec_point.clone(), v)])
        .collect::<Vec<_>>();
    for values in &dp_values {
        for &v in values {
            initial_statements.push(vec![Evaluation::new(dp_point.clone(), v)]);
        }
    }

    let mut prover_state = build_prover_state();

    let statements = packed_pcs_global_statements_for_prover(
        &all_colums_ref,
        &all_dims,
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
        &initial_statements,
        &mut prover_state,
    );

    // sanitiy check
    for statement in &statements {
        assert_eq!(
            packed_polynomial.evaluate_sparse(&statement.point),
            statement.value
        );
    }
}
