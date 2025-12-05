use crate::{EF, ExtraDataForBuses, F, Poseidon16Precompile, tables::poseidon_16::trace_gen::generate_trace_rows_16};
use air::{check_air_validity, prove_air, verify_air};
use multilinear_toolkit::prelude::*;
use rand::{Rng, SeedableRng, rngs::StdRng};
use utils::{build_prover_state, build_verifier_state};

const UNIVARIATE_SKIPS: usize = 3;

#[test]
fn test_benchmark_air_poseidon_16() {
    benchmark_air_poseidon_16(12);
}

pub fn benchmark_air_poseidon_16(log_n_rows: usize) {
    let n_rows = 1 << log_n_rows;
    let mut rng = StdRng::seed_from_u64(0);
    let input: [Vec<F>; 16] = std::array::from_fn(|_| (0..n_rows).map(|_| rng.random()).collect());
    let index_a: Vec<F> = (0..n_rows).map(|_| rng.random()).collect();
    let index_b: Vec<F> = (0..n_rows).map(|_| rng.random()).collect();
    let index_res: Vec<F> = (0..n_rows).map(|_| rng.random()).collect();
    let compress: Vec<F> = (0..n_rows).map(|_| F::from_bool(rng.random())).collect();
    let trace = generate_trace_rows_16(&input, &index_a, &index_b, &index_res, &compress);
    assert_eq!(trace[0].len(), n_rows);

    let air = Poseidon16Precompile::<false>;

    check_air_validity(
        &air,
        &ExtraDataForBuses::default(),
        &trace.iter().map(|row| row.as_slice()).collect::<Vec<_>>(),
        &[] as &[&[EF]],
        &[],
        &[],
    )
    .unwrap();

    let mut prover_state = build_prover_state(false);
    let prover_statements = prove_air::<EF, _>(
        &mut prover_state,
        &air,
        ExtraDataForBuses::default(),
        UNIVARIATE_SKIPS,
        &trace.iter().map(|row| row.as_slice()).collect::<Vec<_>>(),
        &[] as &[&[EF]],
        &[],
        &[],
        None,
        true,
    );

    let mut verifier_state = build_verifier_state(prover_state);
    let verifier_statements = verify_air(
        &mut verifier_state,
        &air,
        ExtraDataForBuses::default(),
        UNIVARIATE_SKIPS,
        log_n_rows,
        &[],
        &[],
        None,
    )
    .unwrap();
}
