use lookup::{compute_pushforward, prove_logup_star, verify_logup_star};
use multilinear_toolkit::prelude::*;
use p3_field::PrimeCharacteristicRing;
use p3_koala_bear::{KoalaBear, QuinticExtensionFieldKB};
use p3_util::log2_ceil_usize;
use packed_pcs::{ColDims, MultilinearChunks, packed_pcs_global_statements_for_prover};
use rand::{Rng, SeedableRng, rngs::StdRng};
use utils::{ToUsize, build_prover_state, build_verifier_state};

type F = KoalaBear;
type EF = QuinticExtensionFieldKB;
const LOG_SMALLEST_DECOMPOSITION_CHUNK: usize = 5;

#[test]
fn test_packed_lookup() {
    let memory_size: usize = 37412;
    let lookups_num_lines_and_cols: Vec<(usize, usize)> =
        vec![(4587, 1), (1234, 3), (9411, 1), (7890, 2)];
    let default_indexes = vec![7, 11, 0, 2];
    assert_eq!(lookups_num_lines_and_cols.len(), default_indexes.len());

    let mut rng = StdRng::seed_from_u64(0);
    let mut memory = F::zero_vec(memory_size.next_power_of_two());
    for i in 1..memory_size {
        memory[i] = rng.random();
    }

    let mut all_indexe_columns = vec![];
    let mut all_value_columns = vec![];
    let mut all_points = vec![];
    let mut all_evaluations = vec![];
    for (i, (n_lines, n_cols)) in lookups_num_lines_and_cols.iter().enumerate() {
        let mut indexes = vec![F::from_usize(default_indexes[i]); n_lines.next_power_of_two()];
        for i in 0..*n_lines {
            indexes[i] = F::from_usize(rng.random_range(0..memory_size));
        }
        all_indexe_columns.push(indexes);
        let indexes = all_indexe_columns.last().unwrap();

        let point = MultilinearPoint(
            (0..log2_ceil_usize(*n_lines))
                .map(|_| rng.random())
                .collect::<Vec<EF>>(),
        );
        all_points.push(point.clone());

        let mut columns = vec![];
        let mut evaluations = vec![];
        for col_index in 0..*n_cols {
            let mut col = F::zero_vec(n_lines.next_power_of_two());
            for i in 0..n_lines.next_power_of_two() {
                col[i] = memory[indexes[i].to_usize() + col_index];
            }
            evaluations.push(col.evaluate(&point));
            columns.push(col);
        }
        all_evaluations.push(evaluations);
        all_value_columns.push(columns);
    }

    let mut all_dims = vec![];
    for (i, (n_lines, n_cols)) in lookups_num_lines_and_cols.iter().enumerate() {
        for col_index in 0..*n_cols {
            all_dims.push(ColDims::padded(*n_lines, memory[col_index + default_indexes[i]]));
        }
    }

    let all_value_columns_ref = all_value_columns
        .iter()
        .flat_map(|cols| cols.iter().map(|col| col.as_slice()))
        .collect::<Vec<&[F]>>();

    let mut all_indexes_columns_field = vec![];
    for (indexes, (_, n_cols)) in all_indexe_columns
        .iter()
        .zip(lookups_num_lines_and_cols.iter())
    {
        for col_index in 0..*n_cols {
            let col_field = indexes
                .iter()
                .map(|&i| i + F::from_usize(col_index))
                .collect::<Vec<F>>();
            all_indexes_columns_field.push(col_field);
        }
    }
    let all_indexes_columns_field_ref = all_indexes_columns_field
        .iter()
        .map(|col| col.as_slice())
        .collect::<Vec<&[F]>>();

    let (packed_lookup_values, chunks) = packed_pcs::compute_multilinear_chunks_and_apply(
        &all_value_columns_ref,
        &all_dims,
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
    );

    let mut initial_statements = vec![];
    for (point, evaluations) in all_points.iter().zip(all_evaluations.iter()) {
        for &evaluation in evaluations {
            initial_statements.push(vec![Evaluation::new(point.clone(), evaluation)]);
        }
    }

    let mut prover_state = build_prover_state();

    {
        let statements = packed_pcs_global_statements_for_prover(
            &all_value_columns_ref,
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

        let packed_lookup_indexes = chunks.apply(&all_indexes_columns_field_ref);

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

    let mut verifier_state = build_verifier_state(&prover_state);

    {
        let statements = packed_pcs::packed_pcs_global_statements_for_verifier(
            &all_dims,
            LOG_SMALLEST_DECOMPOSITION_CHUNK,
            &initial_statements,
            &mut verifier_state,
            &Default::default(),
        )
        .unwrap();
        let all_chunks = MultilinearChunks::compute(&all_dims, LOG_SMALLEST_DECOMPOSITION_CHUNK);

        let batching_scalar = verifier_state.sample();

        // receive commitment to pushforward
        let pushforward = verifier_state
            .receive_hint_extension_scalars(memory_size.next_power_of_two())
            .unwrap();

        let logup_star_statements = verify_logup_star(
            &mut verifier_state,
            log2_ceil_usize(memory_size),
            all_chunks.packed_n_vars,
            &statements,
            batching_scalar,
        )
        .unwrap();

        assert_eq!(
            memory.evaluate(&logup_star_statements.on_table.point),
            logup_star_statements.on_table.value
        );
        for pusforward_statement in &logup_star_statements.on_pushforward {
            assert_eq!(
                pushforward.evaluate(&pusforward_statement.point),
                pusforward_statement.value
            );
        }

        let mut value_on_packed_indexes = EF::ZERO;
        let mut offset = 0;
        for (i, (_n_lines, n_cols)) in lookups_num_lines_and_cols.iter().enumerate() {
            let my_chunks = &chunks[offset..offset + n_cols];
            offset += n_cols;

            assert!(my_chunks.iter().all(|col_chunks| {
                col_chunks.iter().zip(my_chunks[0].iter()).all(|(c1, c2)| {
                    c1.offset_in_original == c2.offset_in_original && c1.n_vars == c2.n_vars
                })
            }));
            let mut inner_evals = vec![];
            for chunk in &my_chunks[0] {
                inner_evals.push(
                    (&all_indexe_columns[i][chunk.offset_in_original..][..1 << chunk.n_vars])
                        .evaluate(&MultilinearPoint(
                            logup_star_statements.on_indexes.point
                                [all_chunks.packed_n_vars - chunk.n_vars..]
                                .to_vec(),
                        )),
                );
            }
            for (col_index, chunks_for_col) in my_chunks.iter().enumerate() {
                for (&inner_eval, chunk) in inner_evals.iter().zip(chunks_for_col) {
                    let missing_vars = all_chunks.packed_n_vars - chunk.n_vars;
                    value_on_packed_indexes += (inner_eval + F::from_usize(col_index))
                        * MultilinearPoint(
                            logup_star_statements.on_indexes.point[..missing_vars].to_vec(),
                        )
                        .eq_poly_outside(&MultilinearPoint(
                            chunk.bits_offset_in_packed(all_chunks.packed_n_vars),
                        ));
                }
            }
        }
        assert_eq!(
            value_on_packed_indexes,
            logup_star_statements.on_indexes.value
        );
    }
}
