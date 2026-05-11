use std::time::Instant;

use backend::*;
use lean_vm::{
    DIGEST_LEN, EF, ExtraDataForBuses, F, HALF_DIGEST_LEN, POSEIDON_16_COL_COMPRESSED_OUTPUT_START,
    POSEIDON_16_COL_EFF_SECOND_START, POSEIDON_16_COL_EFFECTIVE_INDEX_LEFT_FIRST,
    POSEIDON_16_COL_EFFECTIVE_INDEX_LEFT_SECOND, POSEIDON_16_COL_FLAG, POSEIDON_16_COL_GKR_START,
    POSEIDON_16_COL_INPUT_START, POSEIDON_16_N_AIR_COLS, POSEIDON_16_N_COMMITTED_COLS, Poseidon16Precompile,
    fill_trace_poseidon_16,
};
use poseidon_gkr::{POSEIDON_16_N_GKR_COLS, prove_poseidon_gkr, verify_poseidon_gkr};
use rand::{RngExt, SeedableRng, rngs::StdRng};
use sub_protocols::{
    AirSumcheckSession, OuterSumcheckSession, natural_ordering_point_for_session, prove_batched_air_sumcheck,
};
use utils::{build_prover_state, build_verifier_state, padd_with_zero_to_next_power_of_two};

const WIDTH: usize = 16;

#[test]
fn test_prove_poseidon_16() {
    // LOG_N_ROWS=20 cargo test --release --package sub_protocols --test prove_poseidon_16 -- test_prove_poseidon_16 --exact --nocapture
    let log_n_rows: usize = std::env::var("LOG_N_ROWS").unwrap_or("11".to_string()).parse().unwrap();
    prove_poseidon_16(log_n_rows);
}

#[allow(clippy::too_many_lines)]
fn prove_poseidon_16(log_n_rows: usize) {
    let n_rows = 1 << log_n_rows;
    let mut rng = StdRng::seed_from_u64(0);

    let n_total_cols = POSEIDON_16_N_COMMITTED_COLS + POSEIDON_16_N_GKR_COLS;
    let mut trace = vec![vec![F::ZERO; n_rows]; n_total_cols];

    for t in trace.iter_mut().skip(POSEIDON_16_COL_INPUT_START).take(WIDTH) {
        *t = (0..n_rows).map(|_| rng.random()).collect();
    }
    trace[POSEIDON_16_COL_FLAG] = vec![F::ONE; n_rows];
    trace[POSEIDON_16_COL_EFFECTIVE_INDEX_LEFT_FIRST] = vec![F::ZERO; n_rows];
    trace[POSEIDON_16_COL_EFFECTIVE_INDEX_LEFT_SECOND] = vec![F::from_usize(HALF_DIGEST_LEN); n_rows];

    fill_trace_poseidon_16(&mut trace);

    for i in 0..HALF_DIGEST_LEN {
        trace[POSEIDON_16_COL_EFF_SECOND_START + i] =
            trace[POSEIDON_16_COL_COMPRESSED_OUTPUT_START + HALF_DIGEST_LEN + i].clone();
    }

    let air = Poseidon16Precompile::<false>;
    let n_constraints = air.n_constraints();
    let air_degree = air.degree_air();
    let n_air = POSEIDON_16_N_AIR_COLS;
    let n_committed = POSEIDON_16_N_COMMITTED_COLS;

    let whir_config_builder = WhirConfigBuilder {
        folding_factor: FoldingFactor::new(7, 4),
        soundness_type: SecurityAssumption::JohnsonBound,
        pow_bits: 16,
        max_num_variables_to_send_coeffs: 9,
        rs_domain_initial_reduction_factor: 5,
        security_level: 124,
        starting_log_inv_rate: 1,
    };

    // Commit to the committed columns (AIR cols + 16 inputs). The GKR-layer columns are
    // non-committed: GKR re-proves them.
    let packed_n_vars = log2_ceil_usize(n_committed << log_n_rows);
    let whir_config = WhirConfig::new(&whir_config_builder, packed_n_vars);

    let mut prover_state = build_prover_state();

    let time = Instant::now();

    let mut commitmed_pol = F::zero_vec((n_committed << log_n_rows).next_power_of_two());
    for (i, col) in trace.iter().take(n_committed).enumerate() {
        commitmed_pol[i << log_n_rows..(i + 1) << log_n_rows].copy_from_slice(col);
    }
    let committed_pol = MleOwned::Base(commitmed_pol);
    let witness = whir_config.commit(&mut prover_state, &committed_pol, n_committed << log_n_rows);

    let alpha = prover_state.sample();
    let air_alpha_powers: Vec<EF> = alpha.powers().collect_n(n_constraints + 1);
    // BUS=false => `logup_alphas_eq_poly` and `bus_beta` are unused; only `alpha_powers` matter.
    let extra_data = ExtraDataForBuses::new(Vec::new(), EF::ZERO, air_alpha_powers);
    let eq_factor: Vec<EF> = prover_state.sample_vec(log_n_rows);
    let column_refs: Vec<&[F]> = trace.iter().take(n_air).map(Vec::as_slice).collect();
    let packed = MleGroupRef::<EF>::Base(column_refs).pack();

    let mut sessions: Vec<Box<dyn OuterSumcheckSession<EF> + '_>> = vec![Box::new(AirSumcheckSession::new(
        packed,
        eq_factor,
        EF::ZERO,
        air,
        extra_data,
        n_rows,
    ))];

    let sumcheck_air_point = prove_batched_air_sumcheck(&mut prover_state, &mut sessions, EF::ONE);
    let col_evals = sessions[0].final_column_evals();
    prover_state.add_extension_scalars(&col_evals);

    let natural_ordering_point = natural_ordering_point_for_session(&sumcheck_air_point.0, log_n_rows);
    let natural_ordering_mp = MultilinearPoint(natural_ordering_point.clone());
    // The AIR sumcheck only produces evals for cols 0..n_air. Send the eval of the remaining
    // committed columns (the 16 inputs) at `natural_ordering_point` so the WHIR statement covers
    // every committed column.
    let input_evals_at_sumcheck: Vec<EF> = (n_air..n_committed)
        .map(|i| (&trace[i][..]).evaluate(&natural_ordering_mp))
        .collect();
    prover_state.add_extension_scalars(&input_evals_at_sumcheck);
    let mut all_committed_evals = col_evals.clone();
    all_committed_evals.extend_from_slice(&input_evals_at_sumcheck);
    let betas: Vec<EF> = prover_state.sample_vec(log2_ceil_usize(n_committed));
    let packed_point = MultilinearPoint([betas.clone(), natural_ordering_point].concat());
    let packed_eval =
        padd_with_zero_to_next_power_of_two(&all_committed_evals).evaluate(&MultilinearPoint(betas));

    whir_config.prove(
        &mut prover_state,
        vec![SparseStatement::dense(packed_point, packed_eval)],
        witness,
        &committed_pol.by_ref(),
    );

    // ---- Poseidon GKR sub-protocol ----
    // Pick a fresh output-layer claim point and send compressed_output / input evals at it
    // (in production these come from logup; here we make the GKR test self-contained).
    let gkr_output_point: MultilinearPoint<EF> = MultilinearPoint(prover_state.sample_vec(log_n_rows));
    let compressed_evals_at_op: Vec<EF> = (0..DIGEST_LEN)
        .map(|i| (&trace[POSEIDON_16_COL_COMPRESSED_OUTPUT_START + i][..]).evaluate(&gkr_output_point))
        .collect();
    let input_evals_at_op: Vec<EF> = (0..DIGEST_LEN)
        .map(|i| (&trace[POSEIDON_16_COL_INPUT_START + i][..]).evaluate(&gkr_output_point))
        .collect();
    prover_state.add_extension_scalars(&compressed_evals_at_op);
    prover_state.add_extension_scalars(&input_evals_at_op);

    let perm_out_0_7: Vec<EF> = (0..DIGEST_LEN)
        .map(|i| compressed_evals_at_op[i] - input_evals_at_op[i])
        .collect();

    let gkr_result = prove_poseidon_gkr::<WIDTH>(
        &mut prover_state,
        &trace,
        POSEIDON_16_COL_INPUT_START,
        POSEIDON_16_COL_GKR_START,
        gkr_output_point,
        &perm_out_0_7,
    );

    println!(
        "{} Poseidons / s",
        (n_rows as f64 / time.elapsed().as_secs_f64()) as usize
    );

    let mut verifier_state = build_verifier_state(prover_state).unwrap();

    let parsed_commitment = whir_config.parse_commitment::<F>(&mut verifier_state).unwrap();

    let alpha = verifier_state.sample();
    let air_alpha_powers: Vec<EF> = alpha.powers().collect_n(n_constraints + 1);
    let extra_data = ExtraDataForBuses::new(Vec::new(), EF::ZERO, air_alpha_powers);

    let eq_factor_v: Vec<EF> = verifier_state.sample_vec(log_n_rows);

    let Evaluation {
        point: sumcheck_air_point_v,
        value: claimed_air_final_value,
    } = sumcheck_verify(&mut verifier_state, log_n_rows, air_degree + 1, EF::ZERO, None).unwrap();

    let col_evals_v: Vec<EF> = verifier_state.next_extension_scalars_vec(n_air).unwrap();
    let constraint_eval =
        <Poseidon16Precompile<false> as SumcheckComputation<EF>>::eval_extension(&air, &col_evals_v, &extra_data);

    let natural_ordering_point_v = natural_ordering_point_for_session(&sumcheck_air_point_v.0, log_n_rows);
    let eq_val = MultilinearPoint(eq_factor_v).eq_poly_outside(&MultilinearPoint(natural_ordering_point_v.clone()));
    assert_eq!(eq_val * constraint_eval, claimed_air_final_value);

    let input_evals_at_sumcheck_v = verifier_state.next_extension_scalars_vec(n_committed - n_air).unwrap();
    let mut all_committed_evals_v = col_evals_v.clone();
    all_committed_evals_v.extend_from_slice(&input_evals_at_sumcheck_v);

    let betas_v: Vec<EF> = verifier_state.sample_vec(log2_ceil_usize(n_committed));
    let packed_point_v = MultilinearPoint([betas_v.clone(), natural_ordering_point_v].concat());
    let packed_eval_v = padd_with_zero_to_next_power_of_two(&all_committed_evals_v).evaluate(&MultilinearPoint(betas_v));

    whir_config
        .verify(
            &mut verifier_state,
            &parsed_commitment,
            vec![SparseStatement::dense(packed_point_v, packed_eval_v)],
        )
        .unwrap();

    // Verifier replays the GKR sub-protocol.
    let gkr_output_point_v: MultilinearPoint<EF> = MultilinearPoint(verifier_state.sample_vec(log_n_rows));
    let compressed_evals_v = verifier_state.next_extension_scalars_vec(DIGEST_LEN).unwrap();
    let input_evals_v = verifier_state.next_extension_scalars_vec(DIGEST_LEN).unwrap();
    let perm_out_0_7_v: Vec<EF> = (0..DIGEST_LEN)
        .map(|i| compressed_evals_v[i] - input_evals_v[i])
        .collect();

    let gkr_result_v =
        verify_poseidon_gkr::<WIDTH>(&mut verifier_state, log_n_rows, &gkr_output_point_v, &perm_out_0_7_v).unwrap();

    // Cross-check the input claims derived by the verifier against the actual committed inputs
    // (in production this is done via a WHIR opening on the input columns).
    assert_eq!(gkr_result.input_point, gkr_result_v.input_point);
    for i in 0..WIDTH {
        let actual_input_eval =
            (&trace[POSEIDON_16_COL_INPUT_START + i][..]).evaluate(&gkr_result_v.input_point);
        assert_eq!(gkr_result_v.input_evals[i], actual_input_eval);
    }
}
