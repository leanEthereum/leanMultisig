use std::array;

use multilinear_toolkit::prelude::*;
use p3_koala_bear::{KoalaBear, QuinticExtensionFieldKB};
use p3_util::log2_ceil_usize;
use rand::{Rng, SeedableRng, rngs::StdRng};
use sub_protocols::{VectorizedPackedLookupProver, VectorizedPackedLookupVerifier};
use utils::{ToUsize, assert_eq_many, build_prover_state, build_verifier_state};

type F = KoalaBear;
type EF = QuinticExtensionFieldKB;
const LOG_SMALLEST_DECOMPOSITION_CHUNK: usize = 5;

const VECTOR_LEN: usize = 8;

#[test]
fn test_vectorized_packed_lookup() {
    let non_zero_memory_size: usize = 37412;
    let cols_heights: Vec<usize> = vec![785, 1022, 4751];
    let default_indexes = vec![7, 11, 0];
    let n_statements = vec![1, 5, 2];
    assert_eq_many!(cols_heights.len(), default_indexes.len(), n_statements.len());

    let mut rng = StdRng::seed_from_u64(0);
    let mut memory = F::zero_vec(non_zero_memory_size.next_power_of_two());
    for mem in memory.iter_mut().take(non_zero_memory_size).skip(VECTOR_LEN) {
        *mem = rng.random();
    }

    let mut all_indexe_columns = vec![];
    for (i, height) in cols_heights.iter().enumerate() {
        let mut indexes = vec![F::from_usize(default_indexes[i]); height.next_power_of_two()];
        for idx in indexes.iter_mut().take(*height) {
            *idx = F::from_usize(rng.random_range(0..non_zero_memory_size / VECTOR_LEN));
        }
        all_indexe_columns.push(indexes);
    }

    let mut all_value_columns = vec![];
    for index_col in &all_indexe_columns {
        let mut values: [Vec<F>; VECTOR_LEN] = Default::default();
        for index in index_col {
            for i in 0..VECTOR_LEN {
                values[i].push(memory[index.to_usize() * VECTOR_LEN + i]);
            }
        }
        all_value_columns.push(values);
    }

    let mut all_statements = vec![];
    for (value_cols, n_statements) in all_value_columns.iter().zip(&n_statements) {
        let mut statements = vec![];
        for _ in 0..*n_statements {
            let point = MultilinearPoint::<EF>::random(&mut rng, log2_strict_usize(value_cols[0].len()));
            let values = value_cols.iter().map(|col| col.evaluate(&point)).collect::<Vec<EF>>();
            statements.push(MultiEvaluation::new(point, values));
        }
        all_statements.push(statements);
    }

    let mut prover_state = build_prover_state();

    let packed_lookup_prover = VectorizedPackedLookupProver::step_1(
        &mut prover_state,
        &memory,
        all_indexe_columns.iter().map(Vec::as_slice).collect(),
        cols_heights.clone(),
        default_indexes.clone(),
        all_value_columns
            .iter()
            .map(|v| array::from_fn::<_, VECTOR_LEN, _>(|i| v[i].as_slice()))
            .collect(),
        all_statements.clone(),
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
    );

    // phony commitment to pushforward
    prover_state.hint_extension_scalars(packed_lookup_prover.pushforward_to_commit());

    let remaining_claims_to_prove = packed_lookup_prover.step_2(&mut prover_state, non_zero_memory_size);

    let mut verifier_state = build_verifier_state(&prover_state);

    let packed_lookup_verifier = VectorizedPackedLookupVerifier::<_, VECTOR_LEN>::step_1(
        &mut verifier_state,
        cols_heights,
        default_indexes,
        all_statements,
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
        &memory[..100],
    )
    .unwrap();

    // receive commitment to pushforward
    let pushforward = verifier_state
        .receive_hint_extension_scalars(non_zero_memory_size.next_power_of_two() / VECTOR_LEN)
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
