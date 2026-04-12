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
        .unwrap_or(18);
    let num_coeffs = 1 << num_variables;

    let params = WhirConfigBuilder {
        security_level: 123,
        max_num_variables_to_send_coeffs: 9,
        pow_bits: 18,
        folding_factor: FoldingFactor::new(7, 4),
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

    let eval_point = MultilinearPoint((0..num_variables).map(|_| rng.random::<EF>()).collect());
    let eval_value = polynomial.evaluate(&eval_point);
    let statement = Evaluation::new(eval_point, eval_value);

    let mut prover_state = ProverState::new(poseidon16.clone());

    precompute_dft_twiddles::<F>(1 << F::TWO_ADICITY);

    let polynomial: MleOwned<EF> = MleOwned::Base(polynomial);

    let time = Instant::now();
    let witness = params.commit(&mut prover_state, &polynomial, num_coeffs);
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
