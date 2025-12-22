use multilinear_toolkit::prelude::*;
use p3_koala_bear::{KoalaBear, QuinticExtensionFieldKB};
use rand::{Rng, SeedableRng, rngs::StdRng};
use sub_protocols::{prove_generic_logup, verify_generic_logup};
use utils::{
    ToUsize, build_prover_state, build_verifier_state, collect_inner_refs, collect_refs,
    transpose_slice_to_basis_coefficients,
};

type F = KoalaBear;
type EF = QuinticExtensionFieldKB;
const DIM: usize = <EF as BasedVectorSpace<PF<EF>>>::DIMENSION;
const LOG_SMALLEST_DECOMPOSITION_CHUNK: usize = 5;

#[test]
fn test_generic_logup() {
    let log_memory_size: usize = 13;
    let log_cols_heights_f: Vec<usize> = vec![12, 11, 13, 1];
    let num_values_per_lookup_f: Vec<usize> = vec![1, 2, 10, 3];
    let log_cols_heights_ef: Vec<usize> = vec![8, 10];
    let bus_n_vars: Vec<usize> = vec![5, 8, 3];
    let univariate_skips: usize = 3;
    assert_eq!(log_cols_heights_f.len(), num_values_per_lookup_f.len());

    let mut rng = StdRng::seed_from_u64(0);
    let mut memory = (0..(1 << log_memory_size))
        .map(|_| rng.random::<F>())
        .collect::<Vec<_>>();
    memory[0] = F::ZERO;

    let mut acc = F::zero_vec(1 << log_memory_size);

    let mut all_indexe_columns_f = vec![];
    let mut all_indexe_columns_ef = vec![];
    for log_height in log_cols_heights_f.iter() {
        let indexes = (0..(1 << log_height))
            .map(|_| {
                F::from_usize(
                    rng.random_range(0..(1 << log_memory_size) - *num_values_per_lookup_f.iter().max().unwrap()),
                )
            })
            .collect::<Vec<F>>();
        all_indexe_columns_f.push(indexes);
    }

    for log_height in log_cols_heights_ef.iter() {
        let indexes = (0..(1 << log_height))
            .map(|_| {
                F::from_usize(rng.random_range(0..(1 << log_memory_size) - <EF as BasedVectorSpace<PF<EF>>>::DIMENSION))
            })
            .collect::<Vec<F>>();
        all_indexe_columns_ef.push(indexes);
    }

    let mut value_columns_f = vec![];
    for (base_col, num_value_cols) in all_indexe_columns_f.iter().zip(num_values_per_lookup_f.iter()) {
        let mut value_cols = vec![];
        for i in 0..*num_value_cols {
            let mut values_col = vec![];
            for index in base_col {
                let index = index.to_usize() + i;
                values_col.push(memory[index]);
                acc[index] += F::ONE;
            }
            value_cols.push(values_col);
        }
        value_columns_f.push(value_cols);
    }
    let mut value_columns_ef = vec![];
    for ext_col in &all_indexe_columns_ef {
        let mut values = vec![];
        for index in ext_col {
            values.push(QuinticExtensionFieldKB::from_basis_coefficients_fn(|i| {
                memory[index.to_usize() + i]
            }));
            for i in 0..<EF as BasedVectorSpace<PF<EF>>>::DIMENSION {
                acc[index.to_usize() + i] += F::ONE;
            }
        }
        value_columns_ef.push(values);
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

    let remaining_claims_to_prove = prove_generic_logup(
        &mut prover_state,
        logup_c,
        logup_alpha,
        &memory,
        &acc,
        collect_refs(&all_indexe_columns_f),
        collect_refs(&all_indexe_columns_ef),
        collect_inner_refs(&value_columns_f),
        collect_refs(&value_columns_ef),
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

    let remaining_claims_to_verify = verify_generic_logup::<EF>(
        &mut verifier_state,
        logup_c,
        logup_alpha,
        log_memory_size,
        log_cols_heights_f,
        num_values_per_lookup_f,
        log_cols_heights_ef,
        bus_n_vars,
        univariate_skips,
    )
    .unwrap();
    assert_eq!(final_prover_state, verifier_state.state());

    assert_eq!(&remaining_claims_to_prove, &remaining_claims_to_verify);

    assert_eq!(
        memory.evaluate(&remaining_claims_to_verify.on_table.point),
        remaining_claims_to_verify.on_table.value
    );
    assert_eq!(
        acc.evaluate(&remaining_claims_to_verify.on_acc.point),
        remaining_claims_to_verify.on_acc.value
    );

    for (index_col, statement) in all_indexe_columns_f
        .iter()
        .zip(remaining_claims_to_verify.on_indexes_f.iter())
    {
        assert_eq!(index_col.evaluate(&statement.point), statement.value);
    }
    for (index_col, statement) in all_indexe_columns_ef
        .iter()
        .zip(remaining_claims_to_verify.on_indexes_ef.iter())
    {
        assert_eq!(index_col.evaluate(&statement.point), statement.value);
    }
    for (i, value_cols) in value_columns_f.iter().enumerate() {
        let statements_for_cols = &remaining_claims_to_verify.on_values_f[i];
        for (col, value) in value_cols.iter().zip(statements_for_cols.values.iter()) {
            assert_eq!(col.evaluate(&statements_for_cols.point), *value);
        }
    }
    for (value_col, value_statements) in value_columns_ef.iter().zip(remaining_claims_to_verify.on_values_ef) {
        let columns_base = transpose_slice_to_basis_coefficients::<PF<EF>, EF>(value_col);
        for (col, value) in columns_base.iter().zip(value_statements.values.iter()) {
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
