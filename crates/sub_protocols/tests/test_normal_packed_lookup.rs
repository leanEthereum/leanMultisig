use std::array;

use multilinear_toolkit::prelude::*;
use p3_koala_bear::{KoalaBear, QuinticExtensionFieldKB};
use rand::{Rng, SeedableRng, rngs::StdRng};
use sub_protocols::{CustomPackedLookupProver, NormalPackedLookupVerifier};
use utils::{ToUsize, build_prover_state, build_verifier_state, collect_refs, transpose_slice_to_basis_coefficients};

type F = KoalaBear;
type EF = QuinticExtensionFieldKB;
const DIM: usize = <EF as BasedVectorSpace<PF<EF>>>::DIMENSION;
const LOG_SMALLEST_DECOMPOSITION_CHUNK: usize = 5;
const VECTOR_LEN: usize = 8;

#[test]
fn test_normal_packed_lookup() {
    let log_memory_size: usize = 12;
    let log_cols_heights_f: Vec<usize> = vec![12, 11, 13, 1];
    let log_cols_heights_ef: Vec<usize> = vec![8, 10];
    let log_cols_heights_vec: Vec<usize> = vec![11, 6, 2];

    let mut rng = StdRng::seed_from_u64(0);
    let mut memory = (0..(1 << log_memory_size))
        .map(|_| rng.random::<F>())
        .collect::<Vec<_>>();
    memory[0] = F::ZERO;

    let mut acc = F::zero_vec(1 << log_memory_size);

    let mut all_indexe_columns_f = vec![];
    let mut all_indexe_columns_ef = vec![];
    let mut all_indexe_columns_vec = vec![];
    for log_height in log_cols_heights_f.iter() {
        let indexes = (0..(1 << log_height))
            .map(|_| F::from_usize(rng.random_range(0..(1 << log_memory_size))))
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
    for log_height in log_cols_heights_vec.iter() {
        let indexes = (0..(1 << log_height))
            .map(|_| F::from_usize(rng.random_range(0..(1 << log_memory_size) / VECTOR_LEN)))
            .collect::<Vec<F>>();
        all_indexe_columns_vec.push(indexes);
    }

    let mut value_columns_f = vec![];
    for base_col in &all_indexe_columns_f {
        let mut values = vec![];
        for index in base_col {
            values.push(memory[index.to_usize()]);
            acc[index.to_usize()] += F::ONE;
        }
        value_columns_f.push(values);
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
    let mut value_columns_vec = vec![];
    for vec_col in &all_indexe_columns_vec {
        let mut values: [Vec<PF<EF>>; VECTOR_LEN] = array::from_fn(|_| vec![]);
        for index in vec_col {
            let base_idx = index.to_usize() * VECTOR_LEN;
            for i in 0..VECTOR_LEN {
                values[i].push(memory[base_idx + i]);
                acc[base_idx + i] += F::ONE;
            }
        }
        value_columns_vec.push(values);
    }

    let mut prover_state = build_prover_state(false);

    let remaining_claims_to_prove = CustomPackedLookupProver::run(
        &mut prover_state,
        &memory,
        &acc,
        collect_refs(&all_indexe_columns_f),
        collect_refs(&all_indexe_columns_ef),
        collect_refs(&all_indexe_columns_vec),
        collect_refs(&value_columns_f),
        collect_refs(&value_columns_ef),
        value_columns_vec
            .iter()
            .map(|cols| array::from_fn(|i| &cols[i][..]))
            .collect(),
    );
    let final_prover_state = prover_state.challenger().state();

    let mut verifier_state = build_verifier_state(prover_state);

    let remaining_claims_to_verify = NormalPackedLookupVerifier::run::<EF, DIM, VECTOR_LEN>(
        &mut verifier_state,
        log_memory_size,
        log_cols_heights_f,
        log_cols_heights_ef,
        log_cols_heights_vec,
    )
    .unwrap();
    assert_eq!(final_prover_state, verifier_state.challenger().state());

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
    for (value_col, statement) in value_columns_f
        .iter()
        .zip(remaining_claims_to_verify.on_values_f.iter())
    {
        assert_eq!(value_col.evaluate(&statement.point), statement.value);
    }
    for (value_col, value_statements) in value_columns_ef.iter().zip(remaining_claims_to_verify.on_values_ef) {
        let columns_base = transpose_slice_to_basis_coefficients::<PF<EF>, EF>(value_col);
        for (col, statement) in columns_base.iter().zip(value_statements.iter()) {
            assert_eq!(col.evaluate(&statement.point), statement.value);
        }
    }
    for (i, value_cols) in value_columns_vec.iter().enumerate() {
        let statements_for_cols = &remaining_claims_to_verify.on_values_vec[i];
        for (col, statement) in value_cols.iter().zip(statements_for_cols.iter()) {
            assert_eq!(col.evaluate(&statement.point), statement.value);
        }
    }
}
