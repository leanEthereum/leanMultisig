use backend::*;
use lean_vm::{
    EF, F, N_TOTAL_COLS_P16, N_TOTAL_COLS_P24, POSEIDON_16_COL_OUTPUT_START, POSEIDON_24_COL_OUTPUT_START,
    POSEIDON_24_OUTPUT_SIZE, ZERO_VEC_PTR,
};
use poseidon_gkr::{fill_poseidon_16_trace, fill_poseidon_24_trace, prove_poseidon_gkr, verify_poseidon_gkr};
use rand::{RngExt, SeedableRng, rngs::StdRng};
use utils::{build_prover_state, build_verifier_state, init_tracing};

const COL_FLAG: usize = 0;
const COL_A: usize = 1;
const COL_B: usize = 2;
const COL_RES: usize = 3;
const COL_INPUT_START: usize = 4;

#[test]
fn test_benchmark_air_poseidon_16() {
    benchmark_prove_poseidon_16(11, false);
}

#[test]
fn test_benchmark_air_poseidon_24() {
    benchmark_prove_poseidon_24(11, false);
}

pub fn benchmark_prove_poseidon_16(log_n_rows: usize, tracing: bool) {
    benchmark_prove_poseidon::<16>(
        log_n_rows,
        tracing,
        N_TOTAL_COLS_P16,
        POSEIDON_16_COL_OUTPUT_START,
        8,
        fill_poseidon_16_trace,
    );
}

pub fn benchmark_prove_poseidon_24(log_n_rows: usize, tracing: bool) {
    benchmark_prove_poseidon::<24>(
        log_n_rows,
        tracing,
        N_TOTAL_COLS_P24,
        POSEIDON_24_COL_OUTPUT_START,
        POSEIDON_24_OUTPUT_SIZE,
        fill_poseidon_24_trace,
    );
}

#[allow(clippy::too_many_lines)]
fn benchmark_prove_poseidon<const WIDTH: usize>(
    log_n_rows: usize,
    tracing: bool,
    n_total_cols: usize,
    col_output_start: usize,
    output_size: usize,
    fill_trace: fn(&mut [Vec<F>]),
) {
    if tracing {
        init_tracing();
    }
    let n_rows = 1 << log_n_rows;
    let mut rng = StdRng::seed_from_u64(0);

    // Generate trace columns
    let mut trace = vec![vec![F::ZERO; n_rows]; n_total_cols];
    for t in trace.iter_mut().skip(COL_INPUT_START).take(WIDTH) {
        *t = (0..n_rows).map(|_| rng.random()).collect();
    }
    trace[COL_FLAG] = (0..n_rows).map(|_| F::ONE).collect();
    trace[COL_RES] = (0..n_rows).map(|_| F::ZERO).collect();
    trace[COL_A] = (0..n_rows).map(|_| F::from_usize(ZERO_VEC_PTR)).collect();
    trace[COL_B] = (0..n_rows).map(|_| F::from_usize(ZERO_VEC_PTR)).collect();

    // Fill GKR layers and compressed outputs
    fill_trace(&mut trace);

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

    let packed_n_vars = log2_ceil_usize(WIDTH << log_n_rows);
    let whir_config = WhirConfig::new(&whir_config, packed_n_vars);

    let time = std::time::Instant::now();

    {
        let mut committed_pol = F::zero_vec(1 << packed_n_vars);
        for i in 0..WIDTH {
            committed_pol[i << log_n_rows..(i + 1) << log_n_rows].copy_from_slice(&trace[COL_INPUT_START + i]);
        }
        let committed_pol = MleOwned::Base(committed_pol);
        let witness = whir_config.commit(&mut prover_state, &committed_pol, WIDTH << log_n_rows);

        // Sample output evaluation point
        let output_point = MultilinearPoint((0..log_n_rows).map(|_| prover_state.sample()).collect());

        // Compute perm_out[0..output_size] = output[i] - input[i] at output_point
        let perm_out_first: Vec<EF> = (0..output_size)
            .map(|i| {
                let out_eval = (&trace[col_output_start + i][..n_rows]).evaluate(&output_point);
                let in_eval = (&trace[COL_INPUT_START + i][..n_rows]).evaluate(&output_point);
                out_eval - in_eval
            })
            .collect();
        prover_state.add_extension_scalars(&perm_out_first);

        // Poseidon GKR proof
        let gkr_result =
            prove_poseidon_gkr::<WIDTH>(&mut prover_state, &trace, output_point, &perm_out_first, output_size);

        // WHIR statement: GKR input evals (WIDTH columns, indexed 0..WIDTH-1)
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
        "{} Poseidon-{WIDTH} / s",
        (n_rows as f64 / time.elapsed().as_secs_f64()) as usize
    );

    {
        let mut verifier_state = build_verifier_state(prover_state).unwrap();

        let parsed_commitment = whir_config.parse_commitment::<F>(&mut verifier_state).unwrap();

        // Sample output evaluation point (same as prover via Fiat-Shamir)
        let output_point = MultilinearPoint((0..log_n_rows).map(|_| verifier_state.sample()).collect());

        // Receive perm_out from prover
        let perm_out_first = verifier_state.next_extension_scalars_vec(output_size).unwrap();

        // GKR verify
        let gkr_result = verify_poseidon_gkr::<WIDTH>(
            &mut verifier_state,
            log_n_rows,
            &output_point,
            &perm_out_first,
            output_size,
        )
        .unwrap();

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
