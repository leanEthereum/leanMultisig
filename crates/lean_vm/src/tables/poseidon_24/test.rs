use crate::{
    EF, ExtraDataForBuses, F, POSEIDON_24_COL_FLAG, POSEIDON_24_COL_INDEX_A, POSEIDON_24_COL_INDEX_A_BIS,
    POSEIDON_24_COL_INDEX_B, POSEIDON_24_COL_INDEX_RES, POSEIDON_24_COL_INDEX_RES_BIS,
    POSEIDON_24_COL_INDEX_RES_BIS_BIS, POSEIDON_24_COL_INPUT_START, POSEIDON_24_NULL_HASH_PTR, Poseidon24Precompile,
    VECTOR_LEN, ZERO_VEC_PTR,
    tables::{
        WIDTH_24, num_cols_24,
        poseidon_24::trace_gen::{default_poseidon_24_row, fill_trace_poseidon_24},
    },
};
use air::{check_air_validity, prove_air, verify_air};
use multilinear_toolkit::prelude::*;
use rand::{Rng, SeedableRng, rngs::StdRng};
use sub_protocols::packed_pcs_global_statements_for_verifier;
use sub_protocols::{ColDims, packed_pcs_global_statements_for_prover};
use sub_protocols::{packed_pcs_commit, packed_pcs_parse_commitment};
use utils::{build_prover_state, build_verifier_state, collect_refs, init_tracing};
use whir_p3::{FoldingFactor, SecurityAssumption, WhirConfig, WhirConfigBuilder};

const UNIVARIATE_SKIPS: usize = 3;
const LOG_SMALLEST_DECOMPOSITION_CHUNK: usize = 13;

#[test]
fn test_benchmark_air_poseidon_24() {
    benchmark_prove_poseidon_24(1026, false);
}

pub fn benchmark_prove_poseidon_24(n_rows: usize, tracing: bool) {
    if tracing {
        init_tracing();
    }
    let mut rng = StdRng::seed_from_u64(0);
    let mut trace = vec![vec![F::ZERO; n_rows]; num_cols_24()];
    for t in trace.iter_mut().skip(POSEIDON_24_COL_INPUT_START).take(WIDTH_24) {
        *t = (0..n_rows).map(|_| rng.random()).collect();
    }
    trace[POSEIDON_24_COL_FLAG] = (0..n_rows).map(|_| F::ONE).collect();
    trace[POSEIDON_24_COL_INDEX_RES] = (0..n_rows).map(|_| F::from_usize(POSEIDON_24_NULL_HASH_PTR)).collect();
    trace[POSEIDON_24_COL_INDEX_RES_BIS] = (0..n_rows)
        .map(|_| F::from_usize(POSEIDON_24_NULL_HASH_PTR + VECTOR_LEN))
        .collect();
    trace[POSEIDON_24_COL_INDEX_RES_BIS_BIS] = (0..n_rows)
        .map(|_| F::from_usize(POSEIDON_24_NULL_HASH_PTR + 2 * VECTOR_LEN))
        .collect();
    trace[POSEIDON_24_COL_INDEX_A] = (0..n_rows).map(|_| F::from_usize(ZERO_VEC_PTR)).collect();
    trace[POSEIDON_24_COL_INDEX_A_BIS] = (0..n_rows).map(|_| F::from_usize(ZERO_VEC_PTR + VECTOR_LEN)).collect();
    trace[POSEIDON_24_COL_INDEX_B] = (0..n_rows).map(|_| F::from_usize(ZERO_VEC_PTR)).collect();
    fill_trace_poseidon_24(&mut trace);

    let default_row = default_poseidon_24_row();

    // padding
    for (col, default_value) in trace.iter_mut().zip(&default_row) {
        col.resize(n_rows.next_power_of_two(), *default_value);
    }
    let dims = default_row
        .iter()
        .map(|v| ColDims::padded(n_rows, *v))
        .collect::<Vec<_>>();
    let whir_config = WhirConfigBuilder {
        folding_factor: FoldingFactor::new(7, 4),
        soundness_type: SecurityAssumption::CapacityBound,
        pow_bits: 16,
        max_num_variables_to_send_coeffs: 6,
        rs_domain_initial_reduction_factor: 5,
        security_level: 128,
        starting_log_inv_rate: 1,
    };

    let air = Poseidon24Precompile::<false>;

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

    let time = std::time::Instant::now();

    let witness = packed_pcs_commit(
        &whir_config,
        &collect_refs(&trace),
        &dims,
        &mut prover_state,
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
    );

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

    let global_statements_prover = packed_pcs_global_statements_for_prover(
        &collect_refs(&trace),
        &dims,
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
        &prover_statements
            .1
            .iter()
            .map(|v| vec![Evaluation::new(prover_statements.0.clone(), *v)])
            .collect::<Vec<_>>(),
        &mut prover_state,
    );

    WhirConfig::new(whir_config.clone(), witness.packed_polynomial.by_ref().n_vars()).prove(
        &mut prover_state,
        global_statements_prover,
        witness.inner_witness,
        &witness.packed_polynomial.by_ref(),
    );

    println!(
        "{} Poseidons / s",
        (n_rows as f64 / time.elapsed().as_secs_f64()) as usize
    );

    let mut verifier_state = build_verifier_state(prover_state);

    let parsed_commitment_base = packed_pcs_parse_commitment(
        &whir_config,
        &mut verifier_state,
        &dims,
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
    )
    .unwrap();

    let verifier_statements = verify_air(
        &mut verifier_state,
        &air,
        ExtraDataForBuses::default(),
        UNIVARIATE_SKIPS,
        log2_ceil_usize(n_rows),
        &[],
        &[],
        None,
    )
    .unwrap();

    let global_statements_verifier = packed_pcs_global_statements_for_verifier(
        &dims,
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
        &verifier_statements
            .1
            .iter()
            .map(|v| vec![Evaluation::new(verifier_statements.0.clone(), *v)])
            .collect::<Vec<_>>(),
        &mut verifier_state,
    )
    .unwrap();

    WhirConfig::new(whir_config, parsed_commitment_base.num_variables)
        .verify(&mut verifier_state, &parsed_commitment_base, global_statements_verifier)
        .unwrap();

    assert_eq!(&prover_statements, &verifier_statements);
    assert!(prover_statements.2.is_empty());
    for (v, col) in prover_statements.1.iter().zip(trace) {
        assert_eq!(col.evaluate(&prover_statements.0), *v);
    }
}
