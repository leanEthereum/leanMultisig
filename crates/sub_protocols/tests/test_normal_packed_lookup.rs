use std::array;

use multilinear_toolkit::prelude::*;
use p3_koala_bear::{KoalaBear, QuinticExtensionFieldKB};
use p3_util::log2_ceil_usize;
use rand::{Rng, SeedableRng, rngs::StdRng};
use sub_protocols::{NormalPackedLookupProver, NormalPackedLookupVerifier};
use utils::{ToUsize, build_prover_state, build_verifier_state, collect_refs, transpose_slice_to_basis_coefficients};

type F = KoalaBear;
type EF = QuinticExtensionFieldKB;
const DIM: usize = <EF as BasedVectorSpace<PF<EF>>>::DIMENSION;
const LOG_SMALLEST_DECOMPOSITION_CHUNK: usize = 5;
const VECTOR_LEN: usize = 8;

#[test]
fn test_normal_packed_lookup() {
    let non_zero_memory_size: usize = 37412;
    let cols_heights_f: Vec<usize> = vec![785, 1022, 4751];
    let cols_heights_ef: Vec<usize> = vec![2088, 110];
    let cols_heights_vec: Vec<usize> = vec![455, 1025, 3333];
    let default_indexes_f = vec![7, 11, 0];
    let default_indexes_ef = vec![2, 3];
    let default_indexes_vec = vec![5, 9, 1];

    let mut rng = StdRng::seed_from_u64(0);
    let mut memory = F::zero_vec(non_zero_memory_size.next_power_of_two());
    for mem in memory.iter_mut().take(non_zero_memory_size).skip(1) {
        *mem = rng.random();
    }

    let mut acc = F::zero_vec(non_zero_memory_size.next_power_of_two());

    let mut all_indexe_columns_f = vec![];
    let mut all_indexe_columns_ef = vec![];
    let mut all_indexe_columns_vec = vec![];
    for (i, height) in cols_heights_f.iter().enumerate() {
        let mut indexes = vec![F::from_usize(default_indexes_f[i]); height.next_power_of_two()];
        for idx in indexes.iter_mut().take(*height) {
            *idx = F::from_usize(rng.random_range(0..non_zero_memory_size));
        }
        all_indexe_columns_f.push(indexes);
    }
    for (i, height) in cols_heights_ef.iter().enumerate() {
        let mut indexes = vec![F::from_usize(default_indexes_ef[i]); height.next_power_of_two()];
        for idx in indexes.iter_mut().take(*height) {
            *idx =
                F::from_usize(rng.random_range(0..non_zero_memory_size - <EF as BasedVectorSpace<PF<EF>>>::DIMENSION));
        }
        all_indexe_columns_ef.push(indexes);
    }
    for (i, height) in cols_heights_vec.iter().enumerate() {
        let mut indexes = vec![F::from_usize(default_indexes_vec[i]); height.next_power_of_two()];
        for idx in indexes.iter_mut().take(*height) {
            *idx = F::from_usize(rng.random_range(0..non_zero_memory_size / VECTOR_LEN));
        }
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

    let remaining_claims_to_prove = NormalPackedLookupProver::run(
        &mut prover_state,
        &memory,
        &mut acc,
        non_zero_memory_size,
        collect_refs(&all_indexe_columns_f),
        collect_refs(&all_indexe_columns_ef),
        collect_refs(&all_indexe_columns_vec),
        cols_heights_f.clone(),
        cols_heights_ef.clone(),
        cols_heights_vec.clone(),
        default_indexes_f.clone(),
        default_indexes_ef.clone(),
        default_indexes_vec.clone(),
        collect_refs(&value_columns_f),
        collect_refs(&value_columns_ef),
        value_columns_vec
            .iter()
            .map(|cols| array::from_fn(|i| &cols[i][..]))
            .collect(),
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
    );
    let final_prover_state = prover_state.challenger().state();

    let mut verifier_state = build_verifier_state(prover_state);

    let remaining_claims_to_verify = NormalPackedLookupVerifier::run::<EF, DIM, VECTOR_LEN>(
        &mut verifier_state,
        log2_ceil_usize(non_zero_memory_size),
        cols_heights_f,
        cols_heights_ef,
        cols_heights_vec,
        default_indexes_f,
        default_indexes_ef,
        default_indexes_vec,
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
        &memory[..100],
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

    for (index_col, index_statements) in all_indexe_columns_f
        .iter()
        .zip(remaining_claims_to_verify.on_indexes_f.iter())
    {
        for statement in index_statements {
            assert_eq!(index_col.evaluate(&statement.point), statement.value);
        }
    }
    for (index_col, index_statements) in all_indexe_columns_ef
        .iter()
        .zip(remaining_claims_to_verify.on_indexes_ef.iter())
    {
        for statement in index_statements {
            assert_eq!(index_col.evaluate(&statement.point), statement.value);
        }
    }
    for (value_col, value_statements) in value_columns_f
        .iter()
        .zip(remaining_claims_to_verify.on_values_f.iter())
    {
        for statement in value_statements {
            assert_eq!(value_col.evaluate(&statement.point), statement.value);
        }
    }
    for (value_col, value_statements) in value_columns_ef.iter().zip(remaining_claims_to_verify.on_values_ef) {
        let columns_base = transpose_slice_to_basis_coefficients::<PF<EF>, EF>(value_col);
        for (col, statements_for_col) in columns_base.iter().zip(value_statements.iter()) {
            for statement in statements_for_col {
                assert_eq!(col.evaluate(&statement.point), statement.value);
            }
        }
    }
    for (i, value_cols) in value_columns_vec.iter().enumerate() {
        let statements_for_cols = &remaining_claims_to_verify.on_values_vec[i];
        for (col, statements_for_col) in value_cols.iter().zip(statements_for_cols.iter()) {
            for statement in statements_for_col {
                assert_eq!(col.evaluate(&statement.point), statement.value);
            }
        }
    }
}
