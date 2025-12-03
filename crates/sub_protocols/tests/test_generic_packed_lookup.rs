use multilinear_toolkit::prelude::*;
use p3_koala_bear::{KoalaBear, QuinticExtensionFieldKB};
use p3_util::log2_ceil_usize;
use rand::{Rng, SeedableRng, rngs::StdRng};
use sub_protocols::{GenericPackedLookupProver, GenericPackedLookupVerifier};
use utils::{ToUsize, assert_eq_many, build_prover_state, build_verifier_state};

type F = KoalaBear;
type EF = QuinticExtensionFieldKB;
const LOG_SMALLEST_DECOMPOSITION_CHUNK: usize = 5;

#[test]
fn test_generic_packed_lookup() {
    let non_zero_memory_size: usize = 37412;
    let lookups_height_and_cols: Vec<(usize, usize)> = vec![(4587, 1), (1234, 3), (9411, 1), (7890, 2)];
    let default_indexes = vec![7, 11, 0, 2];
    assert_eq_many!(lookups_height_and_cols.len(), default_indexes.len());

    let mut rng = StdRng::seed_from_u64(0);
    let mut memory = F::zero_vec(non_zero_memory_size.next_power_of_two());
    for mem in memory.iter_mut().take(non_zero_memory_size).skip(1) {
        *mem = rng.random();
    }

    let mut acc = F::zero_vec(non_zero_memory_size.next_power_of_two());

    let mut all_indexe_columns = vec![];
    let mut all_value_columns = vec![];
    for (i, (n_lines, n_cols)) in lookups_height_and_cols.iter().enumerate() {
        let mut indexes = vec![F::from_usize(default_indexes[i]); n_lines.next_power_of_two()];
        for idx in indexes.iter_mut().take(*n_lines) {
            *idx = F::from_usize(rng.random_range(0..non_zero_memory_size));
        }
        all_indexe_columns.push(indexes);
        let indexes = all_indexe_columns.last().unwrap();

        let mut columns = vec![];
        for col_index in 0..*n_cols {
            let mut col = F::zero_vec(n_lines.next_power_of_two());
            for i in 0..n_lines.next_power_of_two() {
                let idx = indexes[i].to_usize() + col_index;
                col[i] = memory[idx];
                acc[idx] += F::ONE;
            }
            columns.push(col);
        }
        all_value_columns.push(columns);
    }

    let mut prover_state = build_prover_state(false);
    let acc_before = acc.clone();
    let remaining_claims_to_prove = GenericPackedLookupProver::run::<EF>(
        &mut prover_state,
        &memory,
        &mut acc,
        all_indexe_columns.iter().map(Vec::as_slice).collect(),
        lookups_height_and_cols.iter().map(|(h, _)| *h).collect(),
        default_indexes.clone(),
        all_value_columns
            .iter()
            .map(|cols| cols.iter().map(|s| s.as_slice()).collect())
            .collect(),
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
        non_zero_memory_size,
    );
    assert!(acc_before == acc);
    let final_prover_state = prover_state.challenger().state();

    let mut verifier_state = build_verifier_state(prover_state);

    let remaining_claims_to_verify = GenericPackedLookupVerifier::run(
        &mut verifier_state,
        log2_ceil_usize(non_zero_memory_size),
        lookups_height_and_cols.iter().map(|(h, _)| *h).collect(),
        default_indexes,
        lookups_height_and_cols.iter().map(|(_, n_cols)| *n_cols).collect(),
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
        &memory[..100],
    )
    .unwrap();
    let final_verifier_state = verifier_state.challenger().state();

    assert_eq!(&remaining_claims_to_prove, &remaining_claims_to_verify);
    assert_eq!(final_prover_state, final_verifier_state);

    assert_eq!(
        memory.evaluate(&remaining_claims_to_verify.on_table.point),
        remaining_claims_to_verify.on_table.value
    );
    assert_eq!(
        acc.evaluate(&remaining_claims_to_verify.on_acc.point),
        remaining_claims_to_verify.on_acc.value
    );

    for (index_col, index_statements) in all_indexe_columns
        .iter()
        .zip(remaining_claims_to_verify.on_indexes.iter())
    {
        for statement in index_statements {
            assert_eq!(index_col.evaluate(&statement.point), statement.value);
        }
    }
    for (value_cols, value_statements) in all_value_columns
        .iter()
        .zip(remaining_claims_to_verify.on_values.iter())
    {
        for (col, statements_for_col) in value_cols.iter().zip(value_statements.iter()) {
            for statement in statements_for_col {
                assert_eq!(col.evaluate(&statement.point), statement.value);
            }
        }
    }
}
