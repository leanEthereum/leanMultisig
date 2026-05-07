use backend::*;
use lean_vm::{
    DIGEST_LEN, EF, ExtraDataForBuses, F, HALF_DIGEST_LEN, POSEIDON_8_COL_EFFECTIVE_INDEX_LEFT_FIRST,
    POSEIDON_8_COL_EFFECTIVE_INDEX_LEFT_SECOND, POSEIDON_8_COL_FLAG, POSEIDON_8_COL_INPUT_START,
    POSEIDON_8_COL_OUTPUT_START, POSEIDON_8_COL_ROUND_START, Poseidon8Precompile, compute_poseidon8_witness,
    fill_trace_poseidon_8,
};
use rand::{RngExt, SeedableRng, rngs::StdRng};
use sub_protocols::{
    AirSumcheckSession, OuterSumcheckSession, natural_ordering_point_for_session, prove_batched_air_sumcheck,
};
use utils::{build_prover_state, build_verifier_state, init_tracing, padd_with_zero_to_next_power_of_two};

const WIDTH: usize = 8;

#[test]
fn test_benchmark_air_poseidon_8() {
    benchmark_prove_poseidon_8(11, false);
}

#[allow(clippy::too_many_lines, clippy::needless_range_loop)]
pub fn benchmark_prove_poseidon_8(log_n_rows: usize, tracing: bool) {
    if tracing {
        init_tracing();
    }

    let n_rows = 1 << log_n_rows;
    let mut rng = StdRng::seed_from_u64(0);

    let air = Poseidon8Precompile::<false>;
    let n_air_cols = air.n_columns();
    let mut trace = vec![vec![F::ZERO; n_rows]; n_air_cols];

    for row in 0..n_rows {
        let input: [F; WIDTH] = rng.random();
        let (aux, output) = compute_poseidon8_witness(input);

        trace[POSEIDON_8_COL_FLAG][row] = F::ONE;
        // flag_hardcoded_left = 0, offset_hardcoded_left = 0, flag_half_output = 0:
        // virtual index_a = effective_index_left_second - HALF_DIGEST_LEN, and the AIR enforces
        // effective_index_left_first = index_a. Picking first = 0 / second = HALF_DIGEST_LEN
        // satisfies it without forcing a particular memory layout.
        trace[POSEIDON_8_COL_EFFECTIVE_INDEX_LEFT_FIRST][row] = F::ZERO;
        trace[POSEIDON_8_COL_EFFECTIVE_INDEX_LEFT_SECOND][row] = F::from_usize(HALF_DIGEST_LEN);
        for i in 0..WIDTH {
            trace[POSEIDON_8_COL_INPUT_START + i][row] = input[i];
        }
        for i in 0..DIGEST_LEN {
            trace[POSEIDON_8_COL_OUTPUT_START + i][row] = output[i];
        }
        for (i, v) in aux.iter().enumerate() {
            trace[POSEIDON_8_COL_ROUND_START + i][row] = *v;
        }
    }
    fill_trace_poseidon_8(&mut trace);

    let whir_config_builder = WhirConfigBuilder {
        folding_factor: FoldingFactor::new(7, 4),
        soundness_type: SecurityAssumption::JohnsonBound,
        pow_bits: 16,
        max_num_variables_to_send_coeffs: 6,
        rs_domain_initial_reduction_factor: 5,
        security_level: 123,
        starting_log_inv_rate: 1,
    };

    let stacked_n_vars = log2_ceil_usize(n_air_cols << log_n_rows);
    let mut stacked = F::zero_vec(1 << stacked_n_vars);
    for (i, col) in trace.iter().enumerate() {
        stacked[i << log_n_rows..(i + 1) << log_n_rows].copy_from_slice(col);
    }
    let committed_pol = MleOwned::Base(stacked);

    let whir_config = WhirConfig::new(&whir_config_builder, stacked_n_vars);

    precompute_dft_twiddles::<F>(1 << (stacked_n_vars + whir_config_builder.starting_log_inv_rate));

    let mut prover_state = build_prover_state();

    let time = std::time::Instant::now();

    let witness = whir_config.commit(&mut prover_state, &committed_pol, n_air_cols << log_n_rows);

    let air_alpha: EF = prover_state.sample();
    let air_alpha_powers: Vec<EF> = air_alpha.powers().collect_n(air.n_constraints() + 1);
    let eq_factor = prover_state.sample_vec(log_n_rows);
    let air_eta: EF = prover_state.sample();

    let extra_data = ExtraDataForBuses::new(vec![], EF::ZERO, air_alpha_powers);

    let trace_refs: Vec<&[F]> = trace.iter().map(Vec::as_slice).collect();
    let packed = MleGroupRef::<EF>::Base(trace_refs).pack();

    let session = AirSumcheckSession::new(packed, eq_factor, EF::ZERO, air, extra_data, n_rows);
    let mut sessions: Vec<Box<dyn OuterSumcheckSession<EF> + '_>> = vec![Box::new(session)];

    let sumcheck_air_point = prove_batched_air_sumcheck(&mut prover_state, &mut sessions, air_eta);

    let col_evals = sessions[0].final_column_evals();
    prover_state.add_extension_scalars(&col_evals);

    let natural_ordering_point = natural_ordering_point_for_session(&sumcheck_air_point.0, log_n_rows);
    let betas = prover_state.sample_vec(log2_ceil_usize(n_air_cols));
    let packed_point = MultilinearPoint([betas.clone(), natural_ordering_point].concat());
    let packed_eval = padd_with_zero_to_next_power_of_two(&col_evals).evaluate(&MultilinearPoint(betas));

    whir_config.prove(
        &mut prover_state,
        vec![SparseStatement::dense(packed_point, packed_eval)],
        witness,
        &committed_pol.by_ref(),
    );

    println!(
        "{} Poseidons / s",
        (n_rows as f64 / time.elapsed().as_secs_f64()) as usize
    );

    {
        let mut verifier_state = build_verifier_state(prover_state).unwrap();

        let parsed_commitment = whir_config.parse_commitment::<F>(&mut verifier_state).unwrap();

        let air_alpha: EF = verifier_state.sample();
        let air_alpha_powers: Vec<EF> = air_alpha.powers().collect_n(air.n_constraints() + 1);
        let eq_factor = verifier_state.sample_vec(log_n_rows);
        let _air_eta: EF = verifier_state.sample();

        let max_full_degree = air.degree_air() + 1;
        let Evaluation {
            point: sumcheck_air_point,
            value: claimed_sum,
        } = sumcheck_verify(&mut verifier_state, log_n_rows, max_full_degree, EF::ZERO, None).unwrap();

        let n_cols_total = air.n_columns() + air.n_down_columns();
        let col_evals = verifier_state.next_extension_scalars_vec(n_cols_total).unwrap();

        let extra_data = ExtraDataForBuses::new(vec![], EF::ZERO, air_alpha_powers);
        let constraint_eval =
            <Poseidon8Precompile<false> as SumcheckComputation<EF>>::eval_extension(&air, &col_evals, &extra_data);

        let natural_ordering_point = natural_ordering_point_for_session(&sumcheck_air_point.0, log_n_rows);
        let eq_val = MultilinearPoint(eq_factor).eq_poly_outside(&MultilinearPoint(natural_ordering_point.clone()));
        assert_eq!(eq_val * constraint_eval, claimed_sum);

        let betas = verifier_state.sample_vec(log2_ceil_usize(n_air_cols));
        let packed_point = MultilinearPoint([betas.clone(), natural_ordering_point].concat());
        let packed_eval = padd_with_zero_to_next_power_of_two(&col_evals).evaluate(&MultilinearPoint(betas));

        whir_config
            .verify(
                &mut verifier_state,
                &parsed_commitment,
                vec![SparseStatement::dense(packed_point, packed_eval)],
            )
            .unwrap();
    }
}
