use backend::*;
use lean_vm::{
    EF, F, N_TOTAL_COLS_P16, POSEIDON_16_COL_A, POSEIDON_16_COL_B, POSEIDON_16_COL_FLAG, POSEIDON_16_COL_INPUT_START,
    POSEIDON_16_COL_OUTPUT_START, POSEIDON_16_COL_RES, POSEIDON_16_NULL_HASH_PTR, ZERO_VEC_PTR,
};
use poseidon_gkr::{fill_poseidon_trace, prove_poseidon_gkr, verify_poseidon_gkr};
use rand::{Rng, SeedableRng, rngs::StdRng};
use utils::{build_prover_state, build_verifier_state, init_tracing};

const WIDTH: usize = 16;

#[test]
fn test_benchmark_air_poseidon_16() {
    benchmark_prove_poseidon_16(11, false);
}

#[allow(clippy::too_many_lines)]
pub fn benchmark_prove_poseidon_16(log_n_rows: usize, tracing: bool) {
    if tracing {
        init_tracing();
    }
    let n_rows = 1 << log_n_rows;
    let mut rng = StdRng::seed_from_u64(0);

    // Generate trace columns (full 492-column trace)
    let mut trace = vec![vec![F::ZERO; n_rows]; N_TOTAL_COLS_P16];
    for t in trace.iter_mut().skip(POSEIDON_16_COL_INPUT_START).take(WIDTH) {
        *t = (0..n_rows).map(|_| rng.random()).collect();
    }
    trace[POSEIDON_16_COL_FLAG] = (0..n_rows).map(|_| F::ONE).collect();
    trace[POSEIDON_16_COL_RES] = (0..n_rows).map(|_| F::from_usize(POSEIDON_16_NULL_HASH_PTR)).collect();
    trace[POSEIDON_16_COL_A] = (0..n_rows).map(|_| F::from_usize(ZERO_VEC_PTR)).collect();
    trace[POSEIDON_16_COL_B] = (0..n_rows).map(|_| F::from_usize(ZERO_VEC_PTR)).collect();

    // Fill GKR layers and compressed outputs
    fill_poseidon_trace(&mut trace);

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

    // Only commit the 16 input columns
    let packed_n_vars = log2_ceil_usize(WIDTH << log_n_rows);
    let whir_config = WhirConfig::new(&whir_config, packed_n_vars);

    let time = std::time::Instant::now();

    {
        let mut committed_pol = F::zero_vec(1 << packed_n_vars);
        for i in 0..WIDTH {
            committed_pol[i << log_n_rows..(i + 1) << log_n_rows]
                .copy_from_slice(&trace[POSEIDON_16_COL_INPUT_START + i]);
        }
        let committed_pol = MleOwned::Base(committed_pol);
        let witness = whir_config.commit(&mut prover_state, &committed_pol, WIDTH << log_n_rows);

        // Sample output evaluation point
        let output_point = MultilinearPoint((0..log_n_rows).map(|_| prover_state.sample()).collect());

        // Compute perm_out[0..8] = output[i] - input[i] at output_point
        let perm_out_0_7: Vec<EF> = (0..8)
            .map(|i| {
                let out_eval = (&trace[POSEIDON_16_COL_OUTPUT_START + i][..n_rows]).evaluate(&output_point);
                let in_eval = (&trace[POSEIDON_16_COL_INPUT_START + i][..n_rows]).evaluate(&output_point);
                out_eval - in_eval
            })
            .collect();
        prover_state.add_extension_scalars(&perm_out_0_7);

        // Poseidon GKR proof
        let gkr_result = prove_poseidon_gkr::<WIDTH>(&mut prover_state, &trace, output_point, &perm_out_0_7);

        // WHIR statement: GKR input evals (16 columns, indexed 0..15)
        let statements = vec![SparseStatement::new(
            packed_n_vars,
            gkr_result.input_point,
            gkr_result
                .input_evals
                .iter()
                .enumerate()
                .map(|(i, &eval)| SparseValue::new(i, eval))
                .collect(),
        )];

        whir_config.prove(&mut prover_state, statements, witness, &committed_pol.by_ref());
    }

    println!(
        "{} Poseidons / s",
        (n_rows as f64 / time.elapsed().as_secs_f64()) as usize
    );

    {
        let mut verifier_state = build_verifier_state(prover_state);

        let parsed_commitment = whir_config.parse_commitment::<F>(&mut verifier_state).unwrap();

        // Sample output evaluation point (same as prover via Fiat-Shamir)
        let output_point = MultilinearPoint((0..log_n_rows).map(|_| verifier_state.sample()).collect());

        // Receive perm_out[0..7] from prover
        let perm_out_0_7 = verifier_state.next_extension_scalars_vec(8).unwrap();

        // GKR verify
        let gkr_result =
            verify_poseidon_gkr::<WIDTH>(&mut verifier_state, log_n_rows, &output_point, &perm_out_0_7).unwrap();

        // WHIR statement (same as prover)
        let statements = vec![SparseStatement::new(
            packed_n_vars,
            gkr_result.input_point,
            gkr_result
                .input_evals
                .iter()
                .enumerate()
                .map(|(i, &eval)| SparseValue::new(i, eval))
                .collect(),
        )];

        whir_config
            .verify(&mut verifier_state, &parsed_commitment, statements)
            .unwrap();
    }
}
