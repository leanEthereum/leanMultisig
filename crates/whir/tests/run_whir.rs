// Credits: whir-p3 (https://github.com/tcoratger/whir-p3) (MIT and Apache-2.0 licenses).

use std::time::Instant;

use fiat_shamir::{ProverState, VerifierState};
use field::{Field, TwoAdicField};
use koala_bear::{KoalaBear, QuinticExtensionFieldKB, default_koalabear_poseidon1_16};
use mt_whir::*;
use poly::*;
use rand::{RngExt, SeedableRng, rngs::StdRng};
use tracing_forest::{ForestLayer, util::LevelFilter};
use tracing_subscriber::{EnvFilter, Registry, layer::SubscriberExt, util::SubscriberInitExt};

type F = KoalaBear;
type EF = QuinticExtensionFieldKB;

/*
WHIR_NUM_VARIABLES=25 cargo test --release --package mt-whir --test run_whir -- test_run_whir --exact --nocapture
*/

#[test]
fn test_run_whir() {
    if true {
        let env_filter: EnvFilter = EnvFilter::builder()
            .with_default_directive(LevelFilter::INFO.into())
            .from_env_lossy();

        let _ = Registry::default()
            .with(env_filter)
            .with(ForestLayer::default())
            .try_init();
    }
    let poseidon16 = default_koalabear_poseidon1_16();

    let num_variables = std::env::var("WHIR_NUM_VARIABLES")
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(22);
    let num_coeffs = 1 << num_variables;

    let log_memory = num_variables.saturating_sub(5);
    let log_exec = num_variables.saturating_sub(6);
    let log_poseidon = num_variables.saturating_sub(8);
    let log_extop = num_variables.saturating_sub(11);
    let log_bytecode = num_variables.saturating_sub(14).max(1);
    let log_pub_mem = num_variables.saturating_sub(9).max(1);

    let params = WhirConfigBuilder {
        security_level: 123,
        max_num_variables_to_send_coeffs: 8,
        pow_bits: 18,
        folding_factor: FoldingFactor::new(7, 5),
        soundness_type: SecurityAssumption::JohnsonBound,
        starting_log_inv_rate: 2,
        rs_domain_initial_reduction_factor: 5,
    };
    let params = WhirConfig::new(&params, num_variables);

    for (i, round) in params.round_parameters.iter().enumerate() {
        println!("round {}: {} queries", i, round.num_queries);
    }

    let mut rng = StdRng::seed_from_u64(0);
    let polynomial = (0..num_coeffs).map(|_| rng.random::<F>()).collect::<Vec<F>>();

    let random_point = |rng: &mut StdRng, n: usize| MultilinearPoint((0..n).map(|_| rng.random()).collect::<Vec<EF>>());

    let claims: Vec<(usize, usize)> = vec![
        (log_memory, 2),     // memory + memory_acc (logup GKR)
        (log_pub_mem, 1),    // public memory consistency
        (log_bytecode, 1),   // bytecode_acc (logup GKR)
        (log_exec, 8),       // execution table - logup GKR (pc + addr/value cols)
        (log_exec, 20),      // execution table - AIR sumcheck (all 20 cols)
        (log_extop, 6),      // ext-op table - logup GKR
        (log_extop, 29),     // ext-op table - AIR sumcheck
        (log_poseidon, 3),   // poseidon table - logup GKR
        (log_poseidon, 240), // poseidon table - AIR sumcheck (all round cols)
    ];

    let mut statement = Vec::new();

    for &(inner_n_vars, num_cols) in &claims {
        let selector_len = num_variables - inner_n_vars;
        let point = random_point(&mut rng, inner_n_vars);
        let total_slots = 1usize << selector_len;
        let n = num_cols.min(total_slots);
        let mut selectors: Vec<usize> = Vec::with_capacity(n);
        while selectors.len() < n {
            let s = rng.random_range(0..total_slots);
            if !selectors.contains(&s) {
                selectors.push(s);
            }
        }
        statement.push(SparseStatement::new(
            num_variables,
            point.clone(),
            selectors
                .iter()
                .map(|&s| SparseValue {
                    selector: s,
                    value: polynomial.evaluate_sparse(s, &point),
                })
                .collect(),
        ));
    }

    // PC start / end: unique-value openings at fixed offsets (empty point,
    // full-width selector) — mirrors the two `unique_value` statements pushed
    // for the execution table in `stacked_pcs_global_statements`.
    let empty_point = MultilinearPoint(vec![]);
    for &offset in &[0usize, num_coeffs - 1] {
        statement.push(SparseStatement::unique_value(
            num_variables,
            offset,
            polynomial.evaluate_sparse(offset, &empty_point),
        ));
    }

    let mut prover_state = ProverState::new(poseidon16.clone());

    precompute_dft_twiddles::<F>(1 << F::TWO_ADICITY);

    let polynomial: MleOwned<EF> = MleOwned::Base(polynomial);

    let time = Instant::now();
    let witness = params.commit(&mut prover_state, &polynomial);
    let commit_time = time.elapsed();

    let witness_clone = witness.clone();
    let time = Instant::now();
    params.prove(
        &mut prover_state,
        statement.clone(),
        witness_clone,
        &polynomial.by_ref(),
    );
    let pruned_proof = prover_state.into_proof();
    let opening_time_single = time.elapsed();

    let proof_size_single = pruned_proof.proof_size_fe() as f64 * F::bits() as f64 / 8.0;

    let mut verifier_state = VerifierState::<EF, _>::new(pruned_proof, poseidon16.clone()).unwrap();

    let parsed_commitment = params.parse_commitment::<F>(&mut verifier_state).unwrap();

    params
        .verify::<F>(&mut verifier_state, &parsed_commitment, statement.clone())
        .unwrap();

    println!(
        "\nProving time: {} ms (commit: {} ms, opening: {} ms), proof size: {:.2} KiB",
        commit_time.as_millis() + opening_time_single.as_millis(),
        commit_time.as_millis(),
        opening_time_single.as_millis(),
        proof_size_single / 1024.0
    );
}

#[test]
fn display_whir_nb_queries() {
    let first_folding_factor = 7;
    for n_vars in 20..31 {
        for log_inv_rate in 1..5 {
            if n_vars + log_inv_rate - first_folding_factor > F::TWO_ADICITY {
                continue;
            }
            let params = WhirConfigBuilder {
                security_level: 123,
                max_num_variables_to_send_coeffs: 9,
                pow_bits: 18,
                folding_factor: FoldingFactor::new(first_folding_factor, 4),
                soundness_type: SecurityAssumption::JohnsonBound,
                starting_log_inv_rate: log_inv_rate,
                rs_domain_initial_reduction_factor: 5,
            };
            let params = WhirConfig::<EF>::new(&params, n_vars);
            println!(
                "n_vars: {}, log_inv_rate: {}, num_queries: {:?}",
                n_vars,
                log_inv_rate,
                params
                    .round_parameters
                    .iter()
                    .map(|r| r.num_queries)
                    .collect::<Vec<_>>()
            );
        }
    }
}
