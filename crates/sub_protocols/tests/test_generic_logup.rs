use multilinear_toolkit::prelude::*;
use p3_koala_bear::{KoalaBear, QuinticExtensionFieldKB};
use rand::{Rng, SeedableRng, rngs::StdRng};
use sub_protocols::{GenericLogupProver, GenericLogupVerifier};
use utils::{ToUsize, VecOrSlice, build_prover_state, build_verifier_state, collect_refs};

type F = KoalaBear;
type EF = QuinticExtensionFieldKB;
const LOG_SMALLEST_DECOMPOSITION_CHUNK: usize = 5;

#[test]
fn test_generic_logup() {
    let log_memory_size: usize = 12;
    let univariate_skips: usize = 3;
    let lookups_log_height_and_cols: Vec<(usize, usize)> = vec![(11, 1), (3, 3), (0, 2), (5, 1)];
    let bus_n_vars: Vec<usize> = vec![4, 5, 3];

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

    let mut bus_numerators = Vec::new();
    let mut bus_denominators = Vec::new();
    let mut q = EF::ZERO;
    for n_vars in &bus_n_vars {
        let mut selector = Vec::new();
        let mut data = Vec::new();
        for _ in 0..(1 << *n_vars) {
            let num: F = rng.random();
            selector.push(num);
            let d: EF = rng.random();
            data.push(d);
            q += d.inverse() * num;
        }
        bus_numerators.push(selector);
        bus_denominators.push(data);
    }
    let last_num = bus_numerators.last_mut().unwrap().last_mut().unwrap();
    let last_den = bus_denominators.last_mut().unwrap().last_mut().unwrap();
    q -= last_den.inverse() * *last_num;
    *last_num = F::NEG_ONE;
    *last_den = q.inverse();
    let mut prover_state = build_prover_state();
    let logup_c = prover_state.sample();
    prover_state.duplexing();
    let logup_alpha = prover_state.sample();
    prover_state.duplexing();

    let remaining_claims_to_prove = GenericLogupProver::run::<EF>(
        &mut prover_state,
        logup_c,
        logup_alpha,
        &memory,
        &acc,
        all_indexe_columns.iter().map(Vec::as_slice).collect(),
        all_value_columns
            .iter()
            .map(|cols| cols.iter().map(|s| VecOrSlice::Slice(s)).collect())
            .collect(),
        collect_refs(&bus_numerators),
        collect_refs(&bus_denominators),
        univariate_skips,
    );
    let final_prover_state = prover_state.state();

    let mut verifier_state = build_verifier_state(prover_state);
    let logup_c = verifier_state.sample();
    verifier_state.duplexing();
    let logup_alpha = verifier_state.sample();
    verifier_state.duplexing();
    let remaining_claims_to_verify = GenericLogupVerifier::run(
        &mut verifier_state,
        logup_c,
        logup_alpha,
        log_memory_size,
        lookups_log_height_and_cols.iter().map(|(h, _)| *h).collect(),
        lookups_log_height_and_cols.iter().map(|(_, n_cols)| *n_cols).collect(),
        bus_n_vars,
        univariate_skips,
    )
    .unwrap();
    let final_verifier_state = verifier_state.state();

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
        for (col, value) in value_cols.iter().zip(value_statements.values.iter()) {
            assert_eq!(col.evaluate(&value_statements.point), *value);
        }
    }

    let univariate_selectors = univariate_selectors::<PF<EF>>(univariate_skips);

    for (numerators, statement) in bus_numerators
        .iter()
        .zip(remaining_claims_to_verify.on_bus_numerators.iter())
    {
        assert_eq!(
            evaluate_univariate_multilinear::<_, _, _, true>(numerators, &statement.point, &univariate_selectors, None),
            statement.value
        );
    }
    for (denominators, statement) in bus_denominators
        .iter()
        .zip(remaining_claims_to_verify.on_bus_denominators.iter())
    {
        assert_eq!(
            evaluate_univariate_multilinear::<_, _, _, true>(
                denominators,
                &statement.point,
                &univariate_selectors,
                None
            ),
            statement.value
        );
    }
}
