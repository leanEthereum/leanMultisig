// Credits: whir-p3 (https://github.com/tcoratger/whir-p3) (MIT and Apache-2.0 licenses).

use std::time::Instant;

use fiat_shamir::{ProverState, VerifierState};
use field::{Field, TwoAdicField};
use koala_bear::{KoalaBear, QuinticExtensionFieldKB, default_koalabear_poseidon2_16};
use mt_whir::*;
use poly::*;
use rand::{Rng, SeedableRng, rngs::StdRng};
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
    let poseidon16 = default_koalabear_poseidon2_16();

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

    let random_sparse_point = |rng: &mut StdRng, num_variables: usize| {
        let selector_len = rng.random_range(0..num_variables / 2);
        let point = (0..num_variables - selector_len)
            .map(|_| rng.random())
            .collect::<Vec<EF>>();
        (selector_len, MultilinearPoint(point))
    };

    // Sample `num_points` random multilinear points in the Boolean hypercube
    let mut points = (0..7)
        .map(|_| random_sparse_point(&mut rng, num_variables))
        .collect::<Vec<_>>();
    points.push((num_variables, MultilinearPoint(vec![])));

    let mut statement = Vec::new();

    // Add constraints for each sampled point (equality constraints)
    for (selector_len, point) in &points {
        let num_selectors = rng.random_range(1..5);
        let mut selectors = vec![];
        for _ in 0..num_selectors {
            let selector = rng.random_range(0..(1 << selector_len));
            if !selectors.contains(&selector) {
                selectors.push(selector);
            }
        }
        statement.push(SparseStatement::new(
            num_variables,
            point.clone(),
            selectors
                .iter()
                .map(|selector| SparseValue {
                    selector: *selector,
                    value: polynomial.evaluate_sparse(*selector, point),
                })
                .collect(),
        ));
    }

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
    let pruned_proof = prover_state.into_pruned_proof();
    let opening_time_single = time.elapsed();

    let proof_size_single = pruned_proof.proof_size_fe() as f64 * F::bits() as f64 / 8.0;

    let transcript = pruned_proof.restore().unwrap().raw_proof();
    let mut verifier_state = VerifierState::new(transcript, poseidon16.clone());

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
