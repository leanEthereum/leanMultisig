use std::collections::VecDeque;
use std::path::Path;
use std::time::Instant;

use lean_compiler::compile_program;
use lean_prover::prove_execution::prove_execution;
use lean_prover::verify_execution::verify_execution;
use lean_prover::whir_config_builder;
use lean_vm::*;
use multilinear_toolkit::prelude::*;
use rand::Rng;
use rand::SeedableRng;
use rand::rngs::StdRng;
use utils::build_challenger;
use utils::{build_prover_state, padd_with_zero_to_next_multiple_of};
use whir_p3::{FoldingFactor, SecurityAssumption, WhirConfig, WhirConfigBuilder, precompute_dft_twiddles};

const NUM_VARIABLES: usize = 25;

pub fn run_whir_recursion_benchmark(tracing: bool, n_recursions: usize) {
    let src_file = Path::new(env!("CARGO_MANIFEST_DIR")).join("whir_recursion.snark");
    let mut program_str = std::fs::read_to_string(src_file.clone()).unwrap();
    let filepath_str = src_file.to_str().unwrap();
    let recursion_config_builder = WhirConfigBuilder {
        max_num_variables_to_send_coeffs: 6,
        security_level: 128,
        pow_bits: 17,
        folding_factor: FoldingFactor::new(7, 4),
        soundness_type: SecurityAssumption::CapacityBound,
        starting_log_inv_rate: 2,
        rs_domain_initial_reduction_factor: 3,
    };

    program_str = program_str.replace("N_RECURSIONS_PLACEHOLDER", &n_recursions.to_string());

    let mut recursion_config = WhirConfig::<EF>::new(recursion_config_builder.clone(), NUM_VARIABLES);

    // TODO remove overriding this
    {
        recursion_config.committment_ood_samples = 1;
        for round in &mut recursion_config.round_parameters {
            round.ood_samples = 1;
        }
    }

    assert_eq!(recursion_config.committment_ood_samples, 1);
    // println!("Whir parameters: {}", params.to_string());
    for (i, round) in recursion_config.round_parameters.iter().enumerate() {
        program_str = program_str
            .replace(&format!("NUM_QUERIES_{i}_PLACEHOLDER"), &round.num_queries.to_string())
            .replace(&format!("GRINDING_BITS_{i}_PLACEHOLDER"), &round.pow_bits.to_string());
    }
    program_str = program_str
        .replace(
            &format!("NUM_QUERIES_{}_PLACEHOLDER", recursion_config.n_rounds()),
            &recursion_config.final_queries.to_string(),
        )
        .replace(
            &format!("GRINDING_BITS_{}_PLACEHOLDER", recursion_config.n_rounds()),
            &recursion_config.final_pow_bits.to_string(),
        )
        .replace("N_VARS_PLACEHOLDER", &NUM_VARIABLES.to_string())
        .replace(
            "LOG_INV_RATE_PLACEHOLDER",
            &recursion_config_builder.starting_log_inv_rate.to_string(),
        );
    assert_eq!(recursion_config.n_rounds(), 3); // this is hardcoded in the program above
    for round in 0..=recursion_config.n_rounds() {
        program_str = program_str.replace(
            &format!("FOLDING_FACTOR_{round}_PLACEHOLDER"),
            &recursion_config_builder.folding_factor.at_round(round).to_string(),
        );
    }
    program_str = program_str.replace(
        "RS_REDUCTION_FACTOR_0_PLACEHOLDER",
        &recursion_config_builder.rs_domain_initial_reduction_factor.to_string(),
    );

    let mut rng = StdRng::seed_from_u64(0);
    let polynomial = MleOwned::Base((0..1 << NUM_VARIABLES).map(|_| rng.random()).collect::<Vec<F>>());

    let point = MultilinearPoint::<EF>((0..NUM_VARIABLES).map(|_| rng.random()).collect());

    let mut statement = Vec::new();
    let eval = polynomial.evaluate(&point);
    statement.push(Evaluation::new(point.clone(), eval));

    let mut prover_state = build_prover_state(true);

    precompute_dft_twiddles::<F>(1 << 24);

    let witness = recursion_config.commit(&mut prover_state, &polynomial);
    recursion_config.prove(&mut prover_state, statement.clone(), witness, &polynomial.by_ref());
    let whir_proof = prover_state.into_proof();

    {
        let mut verifier_state = VerifierState::new(whir_proof.clone(), build_challenger());
        let parsed_commitment = recursion_config.parse_commitment::<F>(&mut verifier_state).unwrap();
        recursion_config
            .verify(&mut verifier_state, &parsed_commitment, statement)
            .unwrap();
    }

    let commitment_size = 16;
    let mut public_input = whir_proof.proof_data[..commitment_size].to_vec();
    public_input.extend(padd_with_zero_to_next_multiple_of(
        &point
            .iter()
            .flat_map(|x| <EF as BasedVectorSpace<F>>::as_basis_coefficients_slice(x).to_vec())
            .collect::<Vec<F>>(),
        VECTOR_LEN,
    ));
    public_input.extend(padd_with_zero_to_next_multiple_of(
        <EF as BasedVectorSpace<F>>::as_basis_coefficients_slice(&eval),
        VECTOR_LEN,
    ));

    public_input.extend(whir_proof.proof_data[commitment_size..].to_vec());

    assert!(public_input.len().is_multiple_of(VECTOR_LEN));
    program_str = program_str.replace(
        "WHIR_PROOF_SIZE_PLACEHOLDER",
        &(public_input.len() / VECTOR_LEN).to_string(),
    );

    public_input = std::iter::repeat_n(public_input, n_recursions).flatten().collect();

    if tracing {
        utils::init_tracing();
    }

    let bytecode = compile_program(filepath_str, program_str);

    let mut merkle_path_hints = VecDeque::new();
    for _ in 0..n_recursions {
        merkle_path_hints.extend(whir_proof.merkle_hints.clone());
    }

    // in practice we will precompute all the possible values
    // (depending on the number of recursions + the number of xmss signatures)
    // (or even better: find a linear relation)
    let no_vec_runtime_memory = execute_bytecode(
        &bytecode,
        (&public_input, &[]),
        1 << 20,
        false,
        (&vec![], &vec![]), // TODO
        merkle_path_hints.clone(),
    )
    .no_vec_runtime_memory;

    let time = Instant::now();

    let (proof, summary) = prove_execution(
        &bytecode,
        (&public_input, &[]),
        whir_config_builder(),
        no_vec_runtime_memory,
        false,
        (&vec![], &vec![]), // TODO precompute poseidons
        merkle_path_hints,
    );
    let proof_size = proof.proof_size;
    let proving_time = time.elapsed();
    verify_execution(&bytecode, &public_input, proof, whir_config_builder()).unwrap();

    println!("{summary}");
    println!(
        "Proving time: {} ms / WHIR recursion, proof size: {} KiB (not optimized)",
        proving_time.as_millis() / n_recursions as u128,
        proof_size * F::bits() / (8 * 1024)
    );
}

#[test]
fn test_whir_recursion() {
    run_whir_recursion_benchmark(false, 1);
}
