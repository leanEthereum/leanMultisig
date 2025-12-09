use multilinear_toolkit::prelude::*;
use p3_koala_bear::{KoalaBear, QuinticExtensionFieldKB};
use rand::{Rng, SeedableRng, rngs::StdRng};
use sub_protocols::{GeneralizedLogupProver, GeneralizedLogupVerifier};
use utils::{ToUsize, VecOrSlice, build_prover_state, build_verifier_state};

type F = KoalaBear;
type EF = QuinticExtensionFieldKB;
const LOG_SMALLEST_DECOMPOSITION_CHUNK: usize = 5;

#[test]
fn test_generic_logup() {
    let log_memory_size: usize = 12;
    let lookups_log_height_and_cols: Vec<(usize, usize)> = vec![(11, 1), (3, 3), (0, 2), (5, 1)];

    let mut rng = StdRng::seed_from_u64(0);
    let mut memory = (0..(1 << log_memory_size))
        .map(|_| rng.random::<F>())
        .collect::<Vec<_>>();
    memory[0] = F::ZERO;

    let mut acc = F::zero_vec(1 << log_memory_size);

    let mut all_indexe_columns = vec![];
    let mut all_value_columns = vec![];
    for (log_height, n_cols) in &lookups_log_height_and_cols {
        let indexes = (0..(1 << log_height))
            .map(|_| F::from_usize(rng.random_range(0..(1 << log_memory_size))))
            .collect::<Vec<F>>();
        all_indexe_columns.push(indexes);
        let indexes = all_indexe_columns.last().unwrap();

        let mut columns = vec![];
        for col_index in 0..*n_cols {
            let mut col = F::zero_vec(1 << log_height);
            for i in 0..(1 << log_height) {
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
    let remaining_claims_to_prove = GeneralizedLogupProver::run::<EF>(
        &mut prover_state,
        &memory,
        &acc,
        all_indexe_columns.iter().map(Vec::as_slice).collect(),
        all_value_columns
            .iter()
            .map(|cols| cols.iter().map(|s| VecOrSlice::Slice(s)).collect())
            .collect(),
    );
    assert!(acc_before == acc);
    let final_prover_state = prover_state.challenger().state();

    let mut verifier_state = build_verifier_state(prover_state);

    let remaining_claims_to_verify = GeneralizedLogupVerifier::run(
        &mut verifier_state,
        log_memory_size,
        lookups_log_height_and_cols.iter().map(|(h, _)| *h).collect(),
        lookups_log_height_and_cols.iter().map(|(_, n_cols)| *n_cols).collect(),
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

    for (index_col, statement) in all_indexe_columns
        .iter()
        .zip(remaining_claims_to_verify.on_indexes.iter())
    {
        assert_eq!(index_col.evaluate(&statement.point), statement.value);
    }
    for (value_cols, value_statements) in all_value_columns
        .iter()
        .zip(remaining_claims_to_verify.on_values.iter())
    {
        for (col, statement) in value_cols.iter().zip(value_statements.iter()) {
            assert_eq!(col.evaluate(&statement.point), statement.value);
        }
    }
}
