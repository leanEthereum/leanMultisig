use lookup::{compute_pushforward, prove_logup_star};
use multilinear_toolkit::prelude::*;
use p3_field::PrimeCharacteristicRing;
use p3_koala_bear::{KoalaBear, QuinticExtensionFieldKB};
use p3_util::log2_ceil_usize;
use packed_pcs::{ColDims, packed_pcs_global_statements_for_prover};
use rand::{Rng, SeedableRng, rngs::StdRng};
use utils::{ToUsize, build_prover_state};

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
    let n_extension_field_lookups = 5;

    let mut rng = StdRng::seed_from_u64(0);
    let mut memory = F::zero_vec(memory_size.next_power_of_two());
    for i in DIM..memory_size {
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

    let exec_evaluations = execution_table_values
        .iter()
        .map(|col| col.evaluate(&exec_point))
        .collect::<Vec<_>>();

    let dp_evaluations = dot_product_values
        .iter()
        .map(|cols| {
            cols.iter()
                .map(|col| col.evaluate(&dp_point))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();

    let exec_dims = vec![ColDims::padded(n_cycles, F::ZERO); n_lookups_for_execution];
    let dp_dims =
        vec![ColDims::padded(n_dot_product_rows, F::ZERO); DIM * n_extension_field_lookups];

    let all_dims = [exec_dims, dp_dims].concat();

    let all_colum_values_ref = [
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

    let dot_product_all_consecutive_indexes = dot_product_indexes
        .iter()
        .flat_map(|indexes| (0..DIM).map(|d| indexes.iter().map(|i| i + d).collect::<Vec<usize>>()))
        .collect::<Vec<Vec<usize>>>();

    let all_colum_indexes_field = execution_table_indexes
        .par_iter()
        .chain(&dot_product_all_consecutive_indexes)
        .map(|col| {
            col.par_iter()
                .map(|&i| F::from_usize(i))
                .collect::<Vec<F>>()
        })
        .collect::<Vec<Vec<F>>>();
    let all_colum_indexes_field_ref = all_colum_indexes_field
        .iter()
        .map(|col| col.as_slice())
        .collect::<Vec<&[F]>>();

    let (packed_lookup_values, chunks) = packed_pcs::compute_multilinear_chunks_and_apply(
        &all_colum_values_ref,
        &all_dims,
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
    );

    let mut initial_statements = exec_evaluations
        .iter()
        .map(|&v| vec![Evaluation::new(exec_point.clone(), v)])
        .collect::<Vec<_>>();
    for values in &dp_evaluations {
        for &v in values {
            initial_statements.push(vec![Evaluation::new(dp_point.clone(), v)]);
        }
    }

    let mut prover_state = build_prover_state();

    let statements = packed_pcs_global_statements_for_prover(
        &all_colum_values_ref,
        &all_dims,
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
        &initial_statements,
        &mut prover_state,
    );

    // sanitiy check
    for statement in &statements {
        assert_eq!(
            packed_lookup_values.evaluate_sparse(&statement.point),
            statement.value
        );
    }

    let packed_lookup_indexes = chunks.apply(&all_colum_indexes_field_ref);

    // sanity check
    for (i, index) in packed_lookup_indexes.iter().enumerate() {
        assert_eq!(packed_lookup_values[i], memory[index.to_usize()]);
    }

    let batching_scalar = prover_state.sample();

    let mut poly_eq_point = EF::zero_vec(1 << chunks.packed_n_vars);
    for (alpha_power, statement) in batching_scalar.powers().zip(&statements) {
        compute_sparse_eval_eq(&statement.point, &mut poly_eq_point, alpha_power);
    }
    let pushforward = compute_pushforward(
        &packed_lookup_indexes,
        memory_size.next_power_of_two(),
        &poly_eq_point,
    );

    let batched_value = batching_scalar
        .powers()
        .zip(&statements)
        .map(|(alpha_power, statement)| alpha_power * statement.value)
        .sum();

    // phony commitment to pushforward
    prover_state.hint_extension_scalars(&pushforward);

    prove_logup_star(
        &mut prover_state,
        &MleRef::BasePacked(FPacking::<F>::pack_slice(&memory)),
        &packed_lookup_indexes,
        batched_value,
        &poly_eq_point,
        &pushforward,
        Some(memory_size),
    );
}
