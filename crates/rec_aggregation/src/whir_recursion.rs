use std::path::Path;
use std::time::Instant;

use lean_compiler::compile_program;
use lean_prover::SnarkParams;
use lean_prover::prove_execution::prove_execution;
use lean_prover::verify_execution::verify_execution;
use lean_vm::*;
use multilinear_toolkit::prelude::*;
use rand::Rng;
use rand::SeedableRng;
use rand::rngs::StdRng;
use utils::build_prover_state;
use utils::get_poseidon16;
use whir_p3::{FoldingFactor, SecurityAssumption, WhirConfig, WhirConfigBuilder, precompute_dft_twiddles};

pub fn run_whir_recursion_benchmark(n_recursions: usize, num_variables: usize, tracing: bool, vm_profiler: bool) {
    let src_file = Path::new(env!("CARGO_MANIFEST_DIR")).join("whir_recursion.snark");
    let mut program_str = std::fs::read_to_string(src_file.clone()).unwrap();
    let filepath_str = src_file.to_str().unwrap();
    
    let recursion_config_builder = WhirConfigBuilder {
        max_num_variables_to_send_coeffs: 6,
        security_level: 128,
        pow_bits: 16, // should be less than 16 (cf recursion program)
        folding_factor: FoldingFactor::new(7, 4),
        soundness_type: SecurityAssumption::CapacityBound,
        starting_log_inv_rate: 2,
        rs_domain_initial_reduction_factor: 3,
    };

    let recursion_config = WhirConfig::<EF>::new(&recursion_config_builder, num_variables);

    let mut num_queries = vec![];
    let mut ood_samples = vec![];
    let mut grinding_bits = vec![];
    let merkle_heights = (0..=recursion_config.n_rounds())
        .map(|r| recursion_config.merkle_tree_height(r).to_string())
        .collect::<Vec<_>>();
    let mut folding_factors = vec![];
    for round in &recursion_config.round_parameters {
        num_queries.push(round.num_queries.to_string());
        ood_samples.push(round.ood_samples.to_string());
        grinding_bits.push(round.pow_bits.to_string());
        folding_factors.push(round.folding_factor.to_string());
    }
    folding_factors.push(recursion_config.final_round_config().folding_factor.to_string());
    grinding_bits.push(recursion_config.final_pow_bits.to_string());
    num_queries.push(recursion_config.final_queries.to_string());
    let mut rs_reduction_factors = vec![recursion_config_builder.rs_domain_initial_reduction_factor.to_string()];
    rs_reduction_factors.extend(vec!["1".to_string(); recursion_config.n_rounds()]);

    program_str = program_str
        .replace("N_RECURSIONS_PLACEHOLDER", &n_recursions.to_string())
        .replace(
            "MERKLE_HEIGHTS_PLACEHOLDER",
            &format!("[{}]", merkle_heights.join(", ")),
        )
        .replace("NUM_QUERIES_PLACEHOLDER", &format!("[{}]", num_queries.join(", ")))
        .replace(
            "NUM_OOD_COMMIT_PLACEHOLDER",
            &recursion_config.committment_ood_samples.to_string(),
        )
        .replace("NUM_OODS_PLACEHOLDER", &format!("[{}]", ood_samples.join(", ")))
        .replace("GRINDING_BITS_PLACEHOLDER", &format!("[{}]", grinding_bits.join(", ")))
        .replace(
            "FOLDING_FACTORS_PLACEHOLDER",
            &format!("[{}]", folding_factors.join(", ")),
        )
        .replace("N_VARS_PLACEHOLDER", &num_variables.to_string())
        .replace(
            "LOG_INV_RATE_PLACEHOLDER",
            &recursion_config_builder.starting_log_inv_rate.to_string(),
        )
        .replace(
            "FINAL_VARS_PLACEHOLDER",
            &recursion_config.n_vars_of_final_polynomial().to_string(),
        )
        .replace(
            "RS_REDUCTION_FACTORS_PLACEHOLDER",
            &format!("[{}]", rs_reduction_factors.join(", ")),
        );

    let mut rng = StdRng::seed_from_u64(0);
    let polynomial = MleOwned::Base((0..1 << num_variables).map(|_| rng.random()).collect::<Vec<F>>());

    let point = MultilinearPoint::<EF>((0..num_variables).map(|_| rng.random()).collect());

    let mut statement = Vec::new();
    let eval = polynomial.evaluate(&point);
    statement.push(Evaluation::new(point.clone(), eval));

    let mut prover_state = build_prover_state();

    precompute_dft_twiddles::<F>(1 << 24);

    let witness = recursion_config.commit(&mut prover_state, &polynomial);
    let commitment_size = prover_state.proof().len();
    recursion_config.prove(&mut prover_state, statement.clone(), witness, &polynomial.by_ref());
    let whir_proof = prover_state.into_proof();

    {
        let mut verifier_state = VerifierState::<EF, _>::new(whir_proof.clone(), get_poseidon16().clone());
        verifier_state.duplexing();
        let parsed_commitment = recursion_config.parse_commitment::<F>(&mut verifier_state).unwrap();
        recursion_config
            .verify(&mut verifier_state, &parsed_commitment, statement)
            .unwrap();
    }

    let mut public_input = whir_proof[..commitment_size].to_vec();
    public_input.extend(
        &point
            .iter()
            .flat_map(|x| <EF as BasedVectorSpace<F>>::as_basis_coefficients_slice(x).to_vec())
            .collect::<Vec<F>>(),
    );
    public_input.extend(<EF as BasedVectorSpace<F>>::as_basis_coefficients_slice(&eval));

    public_input.extend(whir_proof[commitment_size..].to_vec());

    program_str = program_str.replace("WHIR_PROOF_SIZE_PLACEHOLDER", &public_input.len().to_string());

    public_input = std::iter::repeat_n(public_input, n_recursions).flatten().collect();

    if tracing {
        utils::init_tracing();
    }

    let bytecode = compile_program(filepath_str, program_str);
    let snark_params = SnarkParams::default();
    let time = Instant::now();

    let proof = prove_execution(
        &bytecode,
        (&public_input, &[]),
        &vec![], // TODO precompute poseidons
        &snark_params,
        vm_profiler,
    );
    let proving_time = time.elapsed();
    verify_execution(&bytecode, &public_input, proof.proof, &snark_params).unwrap();
    println!("{}", proof.exec_summary);
    println!(
        "Proving time: {} ms / WHIR recursion, proof size: {} KiB (not optimized)",
        proving_time.as_millis() / n_recursions as u128,
        proof.proof_size_fe * F::bits() / (8 * 1024)
    );
}

#[test]
fn test_whir_recursion() {
    run_whir_recursion_benchmark(1, 18, false, false);
}
