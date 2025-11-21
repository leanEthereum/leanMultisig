use multilinear_toolkit::prelude::*;
use p3_koala_bear::{KoalaBear, QuinticExtensionFieldKB};
use p3_util::log2_ceil_usize;
use rand::{Rng, SeedableRng, rngs::StdRng};
use sub_protocols::{NormalPackedLookupProver, NormalPackedLookupVerifier};
use utils::{ToUsize, build_prover_state, build_verifier_state, collect_refs};

type F = KoalaBear;
type EF = QuinticExtensionFieldKB;
const LOG_SMALLEST_DECOMPOSITION_CHUNK: usize = 5;

#[test]
fn test_normal_packed_lookup() {
    let non_zero_memory_size: usize = 37412;
    let cols_heights_f: Vec<usize> = vec![785, 1022, 4751];
    let cols_heights_ef: Vec<usize> = vec![2088, 110];
    let default_indexes_f = vec![7, 11, 0];
    let default_indexes_ef = vec![2, 3];
    let n_statements_f = vec![1, 5, 2];
    let n_statements_ef = vec![3, 4];

    let mut rng = StdRng::seed_from_u64(0);
    let mut memory = F::zero_vec(non_zero_memory_size.next_power_of_two());
    for mem in memory.iter_mut().take(non_zero_memory_size).skip(1) {
        *mem = rng.random();
    }

    let mut all_indexe_columns_f = vec![];
    let mut all_indexe_columns_ef = vec![];
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
            *idx = F::from_usize(rng.random_range(
                0..non_zero_memory_size - <EF as BasedVectorSpace<PF<EF>>>::DIMENSION,
            ));
        }
        all_indexe_columns_ef.push(indexes);
    }

    let mut value_columns_f = vec![];
    for base_col in &all_indexe_columns_f {
        let mut values = vec![];
        for index in base_col {
            values.push(memory[index.to_usize()]);
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
        }
        value_columns_ef.push(values);
    }

    let mut all_statements_f = vec![];
    for (value_col_f, n_statements) in value_columns_f.iter().zip(&n_statements_f) {
        let mut statements = vec![];
        for _ in 0..*n_statements {
            let point =
                MultilinearPoint::<EF>::random(&mut rng, log2_strict_usize(value_col_f.len()));
            let value = value_col_f.evaluate(&point);
            statements.push(Evaluation::new(point, value));
        }
        all_statements_f.push(statements);
    }
    let mut all_statements_ef = vec![];
    for (value_col_ef, n_statements) in value_columns_ef.iter().zip(&n_statements_ef) {
        let mut statements = vec![];
        for _ in 0..*n_statements {
            let point =
                MultilinearPoint::<EF>::random(&mut rng, log2_strict_usize(value_col_ef.len()));
            let value = value_col_ef.evaluate(&point);
            statements.push(Evaluation::new(point, value));
        }
        all_statements_ef.push(statements);
    }

    let mut prover_state = build_prover_state();

    let packed_lookup_prover = NormalPackedLookupProver::step_1(
        &mut prover_state,
        &memory,
        collect_refs(&all_indexe_columns_f),
        collect_refs(&all_indexe_columns_ef),
        cols_heights_f.clone(),
        cols_heights_ef.clone(),
        default_indexes_f.clone(),
        default_indexes_ef.clone(),
        collect_refs(&value_columns_f),
        collect_refs(&value_columns_ef),
        all_statements_f.clone(),
        all_statements_ef.clone(),
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
    );

    // phony commitment to pushforward
    prover_state.hint_extension_scalars(packed_lookup_prover.pushforward_to_commit());

    let remaining_claims_to_prove =
        packed_lookup_prover.step_2(&mut prover_state, non_zero_memory_size);

    let mut verifier_state = build_verifier_state(&prover_state);

    let packed_lookup_verifier = NormalPackedLookupVerifier::step_1(
        &mut verifier_state,
        cols_heights_f,
        cols_heights_ef,
        default_indexes_f,
        default_indexes_ef,
        all_statements_f,
        all_statements_ef,
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
}
