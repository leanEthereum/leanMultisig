use multilinear_toolkit::prelude::*;
use p3_koala_bear::{KoalaBear, QuinticExtensionFieldKB};
use p3_util::log2_ceil_usize;
use rand::{Rng, SeedableRng, rngs::StdRng};
use sub_protocols::{GenericPackedLookupProver, GenericPackedLookupVerifier};
use utils::{ToUsize, VecOrSlice, assert_eq_many, build_prover_state, build_verifier_state};

type F = KoalaBear;
type EF = QuinticExtensionFieldKB;
const LOG_SMALLEST_DECOMPOSITION_CHUNK: usize = 5;

#[test]
fn test_generic_packed_lookup() {
    let non_zero_memory_size: usize = 37412;
    let lookups_height_and_cols: Vec<(usize, usize)> =
        vec![(4587, 1), (1234, 3), (9411, 1), (7890, 2)];
    let default_indexes = vec![7, 11, 0, 2];
    let n_statements = vec![1, 5, 2, 1];
    assert_eq_many!(
        lookups_height_and_cols.len(),
        default_indexes.len(),
        n_statements.len()
    );

    let mut rng = StdRng::seed_from_u64(0);
    let mut memory = F::zero_vec(non_zero_memory_size.next_power_of_two());
    for i in 1..non_zero_memory_size {
        memory[i] = rng.random();
    }

    let mut all_indexe_columns = vec![];
    let mut all_value_columns = vec![];
    let mut all_statements = vec![];
    for (i, (n_lines, n_cols)) in lookups_height_and_cols.iter().enumerate() {
        let mut indexes = vec![F::from_usize(default_indexes[i]); n_lines.next_power_of_two()];
        for i in 0..*n_lines {
            indexes[i] = F::from_usize(rng.random_range(0..non_zero_memory_size));
        }
        all_indexe_columns.push(indexes);
        let indexes = all_indexe_columns.last().unwrap();

        let mut columns = vec![];
        for col_index in 0..*n_cols {
            let mut col = F::zero_vec(n_lines.next_power_of_two());
            for i in 0..n_lines.next_power_of_two() {
                col[i] = memory[indexes[i].to_usize() + col_index];
            }
            columns.push(col);
        }
        let mut statements = vec![];
        for _ in 0..n_statements[i] {
            let point = MultilinearPoint::<EF>::random(&mut rng, log2_ceil_usize(*n_lines));
            let values = columns
                .iter()
                .map(|col| col.evaluate(&point))
                .collect::<Vec<EF>>();
            statements.push(MultiEvaluation::new(point, values));
        }
        all_statements.push(statements);
        all_value_columns.push(columns);
    }

    let mut prover_state = build_prover_state();

    let packed_lookup_prover = GenericPackedLookupProver::step_1(
        &mut prover_state,
        VecOrSlice::Slice(&memory),
        all_indexe_columns.iter().map(Vec::as_slice).collect(),
        lookups_height_and_cols.iter().map(|(h, _)| *h).collect(),
        default_indexes.clone(),
        all_value_columns
            .iter()
            .map(|cols| cols.iter().map(|s| VecOrSlice::Slice(s)).collect())
            .collect(),
        all_statements.clone(),
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
    );

    // phony commitment to pushforward
    prover_state.hint_extension_scalars(&packed_lookup_prover.pushforward_to_commit());

    let remaining_claims_to_prove =
        packed_lookup_prover.step_2(&mut prover_state, non_zero_memory_size);

    let mut verifier_state = build_verifier_state(&prover_state);

    let packed_lookup_verifier = GenericPackedLookupVerifier::step_1(
        &mut verifier_state,
        lookups_height_and_cols.iter().map(|(h, _)| *h).collect(),
        default_indexes,
        all_statements,
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
        &memory[..100],
    )
    .unwrap();

    // receive commitment to pushforward
    let pushforward = verifier_state
        .receive_hint_extension_scalars(non_zero_memory_size.next_power_of_two())
        .unwrap();

    let remaining_claims_to_verify = packed_lookup_verifier
        .step_2(&mut verifier_state, log2_ceil_usize(non_zero_memory_size))
        .unwrap();

    assert_eq!(&remaining_claims_to_prove, &remaining_claims_to_verify);

    assert_eq!(
        memory.evaluate(&remaining_claims_to_verify.on_table.point),
        remaining_claims_to_verify.on_table.value
    );
    for pusforward_statement in &remaining_claims_to_verify.on_pushforward {
        assert_eq!(
            pushforward.evaluate(&pusforward_statement.point),
            pusforward_statement.value
        );
    }
    for (index_col, index_statements) in all_indexe_columns
        .iter()
        .zip(remaining_claims_to_verify.on_indexes.iter())
    {
        for statement in index_statements {
            assert_eq!(index_col.evaluate(&statement.point), statement.value);
        }
    }
}
