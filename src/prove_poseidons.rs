use air::{prove_air, verify_air};
use backend::*;
use lean_vm::{
    EF, ExtraDataForBuses, F, POSEIDON_16_COL_FLAG, POSEIDON_16_COL_INDEX_INPUT_LEFT, POSEIDON_16_COL_INDEX_INPUT_RES,
    POSEIDON_16_COL_INDEX_INPUT_RIGHT, POSEIDON_16_COL_INPUT_START, POSEIDON_24_COL_INDEX_INPUT_LEFT,
    POSEIDON_24_COL_INDEX_INPUT_RIGHT, POSEIDON_24_COL_INDEX_RES, POSEIDON_24_COL_INPUT_START,
    POSEIDON_24_COL_IS_COMPRESS_0_9, POSEIDON_24_COL_IS_PERMUTE_0_9, Poseidon16Precompile, Poseidon24Precompile,
    ZERO_VEC_PTR, fill_trace_poseidon_16, fill_trace_poseidon_24, num_cols_poseidon_16, num_cols_poseidon_24,
};
use rand::{RngExt, SeedableRng, rngs::StdRng};
use utils::{build_prover_state, build_verifier_state, init_tracing, padd_with_zero_to_next_power_of_two};

#[test]
fn test_benchmark_air_poseidon_16() {
    benchmark_prove_poseidon_16(11, false);
}

#[test]
fn test_benchmark_air_poseidon_24() {
    benchmark_prove_poseidon_24(11, false);
}

pub fn benchmark_prove_poseidon_16(log_n_rows: usize, tracing: bool) {
    if tracing {
        init_tracing();
    }
    let n_rows = 1 << log_n_rows;
    let n_cols = num_cols_poseidon_16();
    let mut rng = StdRng::seed_from_u64(0);

    let mut trace = vec![vec![F::ZERO; n_rows]; n_cols];
    for t in trace.iter_mut().skip(POSEIDON_16_COL_INPUT_START).take(16) {
        *t = (0..n_rows).map(|_| rng.random()).collect();
    }
    trace[POSEIDON_16_COL_FLAG] = vec![F::ONE; n_rows];
    trace[POSEIDON_16_COL_INDEX_INPUT_LEFT] = vec![F::from_usize(ZERO_VEC_PTR); n_rows];
    trace[POSEIDON_16_COL_INDEX_INPUT_RIGHT] = vec![F::from_usize(ZERO_VEC_PTR); n_rows];
    trace[POSEIDON_16_COL_INDEX_INPUT_RES] = vec![F::ZERO; n_rows];

    fill_trace_poseidon_16(&mut trace);

    benchmark_prove_poseidons(log_n_rows, &Poseidon16Precompile::<false>, &trace, n_cols, 16);
}

pub fn benchmark_prove_poseidon_24(log_n_rows: usize, tracing: bool) {
    if tracing {
        init_tracing();
    }
    let n_rows = 1 << log_n_rows;
    let n_committed_cols = num_cols_poseidon_24();
    let n_total_cols = n_committed_cols + 1; // +1 virtual column (precompile_data)
    let mut rng = StdRng::seed_from_u64(0);

    let mut trace = vec![vec![F::ZERO; n_rows]; n_total_cols];
    for t in trace.iter_mut().skip(POSEIDON_24_COL_INPUT_START).take(24) {
        *t = (0..n_rows).map(|_| rng.random()).collect();
    }
    trace[0] = vec![F::ONE; n_rows]; // FLAG
    trace[POSEIDON_24_COL_IS_COMPRESS_0_9] = vec![F::ONE; n_rows]; // compress_0_9 mode for benchmark
    trace[POSEIDON_24_COL_IS_PERMUTE_0_9] = vec![F::ZERO; n_rows];
    trace[POSEIDON_24_COL_INDEX_INPUT_LEFT] = vec![F::from_usize(ZERO_VEC_PTR); n_rows];
    trace[POSEIDON_24_COL_INDEX_INPUT_RIGHT] = vec![F::from_usize(ZERO_VEC_PTR); n_rows];
    trace[POSEIDON_24_COL_INDEX_RES] = vec![F::ZERO; n_rows];

    fill_trace_poseidon_24(&mut trace);

    benchmark_prove_poseidons(log_n_rows, &Poseidon24Precompile::<false>, &trace, n_committed_cols, 24);
}

fn benchmark_prove_poseidons(
    log_n_rows: usize,
    air: &impl Air<ExtraData = ExtraDataForBuses<EF>>,
    trace: &[Vec<F>],
    n_committed_cols: usize,
    width: usize,
) {
    let n_rows = 1 << log_n_rows;
    let committed_trace = &trace[..n_committed_cols];

    // Verify AIR validity
    #[cfg(test)]
    {
        let trace_refs: Vec<&[F]> = committed_trace.iter().map(Vec::as_slice).collect();
        air::check_air_validity::<_, EF>(air, &ExtraDataForBuses::<EF>::default(), &trace_refs).unwrap();
    }

    let whir_config = WhirConfigBuilder {
        folding_factor: FoldingFactor::new(7, 4),
        soundness_type: SecurityAssumption::JohnsonBound,
        pow_bits: 16,
        max_num_variables_to_send_coeffs: 6,
        rs_domain_initial_reduction_factor: 5,
        security_level: 123,
        starting_log_inv_rate: 1,
    };

    let mut prover_state = build_prover_state();
    let packed_n_vars = log2_ceil_usize(n_committed_cols << log_n_rows);
    let whir_config = WhirConfig::new(&whir_config, packed_n_vars);

    let time = std::time::Instant::now();

    {
        let mut committed_pol = F::zero_vec(1 << packed_n_vars);
        for (i, col) in committed_trace.iter().enumerate() {
            committed_pol[i << log_n_rows..(i + 1) << log_n_rows].copy_from_slice(col);
        }
        let committed_pol = MleOwned::Base(committed_pol);
        let witness = whir_config.commit(&mut prover_state, &committed_pol, n_committed_cols << log_n_rows);

        let alpha = prover_state.sample();
        let air_alpha_powers: Vec<EF> = alpha.powers().collect_n(air.n_constraints() + 1);
        let extra_data = ExtraDataForBuses {
            alpha_powers: air_alpha_powers,
            ..Default::default()
        };
        let air_claims = prove_air::<EF, _>(&mut prover_state, air, extra_data, committed_trace, None, true);

        let betas = MultilinearPoint(
            (0..log2_ceil_usize(n_committed_cols))
                .map(|_| prover_state.sample())
                .collect(),
        );
        let packed_point = MultilinearPoint([betas.0.clone(), air_claims.point.0].concat());
        let packed_eval = padd_with_zero_to_next_power_of_two(&air_claims.evals).evaluate(&MultilinearPoint(betas.0));

        let statements = vec![SparseStatement::dense(packed_point, packed_eval)];
        whir_config.prove(&mut prover_state, statements, witness, &committed_pol.by_ref());
    }

    println!(
        "{} Poseidon-{width} / s",
        (n_rows as f64 / time.elapsed().as_secs_f64()) as usize
    );

    {
        let mut verifier_state = build_verifier_state(prover_state).unwrap();
        let parsed_commitment = whir_config.parse_commitment::<F>(&mut verifier_state).unwrap();

        let alpha = verifier_state.sample();
        let air_alpha_powers: Vec<EF> = alpha.powers().collect_n(air.n_constraints() + 1);
        let extra_data = ExtraDataForBuses {
            alpha_powers: air_alpha_powers,
            ..Default::default()
        };
        let air_claims = verify_air(&mut verifier_state, air, extra_data, log_n_rows, None).unwrap();

        let betas = MultilinearPoint(
            (0..log2_ceil_usize(n_committed_cols))
                .map(|_| verifier_state.sample())
                .collect(),
        );
        let packed_point = MultilinearPoint([betas.0.clone(), air_claims.point.0].concat());
        let packed_eval = padd_with_zero_to_next_power_of_two(&air_claims.evals).evaluate(&MultilinearPoint(betas.0));

        let statements = vec![SparseStatement::dense(packed_point, packed_eval)];
        whir_config
            .verify(&mut verifier_state, &parsed_commitment, statements)
            .unwrap();
    }
}
