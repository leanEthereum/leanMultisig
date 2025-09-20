use std::path::Path;
use std::time::{Duration, Instant};

use lean_compiler::compile_program;
use lean_prover::prove_execution::prove_execution;
use lean_prover::verify_execution::verify_execution;
use lean_prover::whir_config_builder;
use lean_vm::*;
use p3_field::BasedVectorSpace;
use p3_field::PrimeCharacteristicRing;
use rand::{Rng, SeedableRng, rngs::StdRng};
use utils::padd_with_zero_to_next_multiple_of;
use utils::padd_with_zero_to_next_power_of_two;
use utils::{build_merkle_compress, build_merkle_hash, build_prover_state, build_verifier_state};
use whir_p3::{
    dft::EvalsDft,
    poly::{evals::EvaluationsList, multilinear::*},
    whir::config::{FoldingFactor, SecurityAssumption, WhirConfig, WhirConfigBuilder},
};

const NUM_VARIABLES: usize = 25;

struct RecursionBenchStats {
    proving_time: Duration,
    proof_size: usize,
}

fn run_recursion_benchmark() -> RecursionBenchStats {
    let src_file = Path::new(env!("CARGO_MANIFEST_DIR")).join("recursion_program.lean_lang");
    let mut program_str = std::fs::read_to_string(src_file).unwrap();
    let recursion_config_builder = WhirConfigBuilder {
        max_num_variables_to_send_coeffs: 6,
        security_level: 128,
        pow_bits: 17,
        folding_factor: FoldingFactor::new(7, 4),
        merkle_hash: build_merkle_hash(),
        merkle_compress: build_merkle_compress(),
        soundness_type: SecurityAssumption::CapacityBound,
        starting_log_inv_rate: 2,
        rs_domain_initial_reduction_factor: 3,
    };

    let mut recursion_config = WhirConfig::new(recursion_config_builder.clone(), NUM_VARIABLES);

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
            .replace(
                &format!("NUM_QUERIES_{i}_PLACEHOLDER"),
                &round.num_queries.to_string(),
            )
            .replace(
                &format!("GRINDING_BITS_{i}_PLACEHOLDER"),
                &round.pow_bits.to_string(),
            );
    }
    program_str = program_str
        .replace(
            &format!("NUM_QUERIES_{}_PLACEHOLDER", recursion_config.n_rounds()),
            &recursion_config.final_queries.to_string(),
        )
        .replace(
            &format!("GRINDING_BITS_{}_PLACEHOLDER", recursion_config.n_rounds()),
            &recursion_config.final_pow_bits.to_string(),
        );
    assert_eq!(recursion_config.n_rounds(), 3); // this is hardcoded in the program above
    for round in 0..=recursion_config.n_rounds() {
        program_str = program_str.replace(
            &format!("FOLDING_FACTOR_{round}_PLACEHOLDER"),
            &recursion_config_builder
                .folding_factor
                .at_round(round)
                .to_string(),
        );
    }
    program_str = program_str.replace(
        "RS_REDUCTION_FACTOR_0_PLACEHOLDER",
        &recursion_config_builder
            .rs_domain_initial_reduction_factor
            .to_string(),
    );

    let mut rng = StdRng::seed_from_u64(0);
    let polynomial = (0..1 << NUM_VARIABLES)
        .map(|_| rng.random())
        .collect::<Vec<F>>();

    let point = MultilinearPoint::<EF>::rand(&mut rng, NUM_VARIABLES);

    let mut statement = Vec::new();
    let eval = polynomial.evaluate(&point);
    statement.push(Evaluation::new(point.clone(), eval));

    let mut prover_state = build_prover_state();

    let dft = EvalsDft::<F>::new(1 << recursion_config.max_fft_size());

    let witness = recursion_config.commit(&dft, &mut prover_state, &polynomial);

    let mut public_input = prover_state.proof_data().to_vec();
    let commitment_size = public_input.len();
    assert_eq!(commitment_size, 16);
    public_input.extend(padd_with_zero_to_next_multiple_of(
        &point
            .iter()
            .flat_map(|x| <EF as BasedVectorSpace<F>>::as_basis_coefficients_slice(x).to_vec())
            .collect::<Vec<F>>(),
        VECTOR_LEN,
    ));
    public_input.extend(padd_with_zero_to_next_power_of_two(
        <EF as BasedVectorSpace<F>>::as_basis_coefficients_slice(&eval),
    ));

    recursion_config.prove(
        &dft,
        &mut prover_state,
        statement.clone(),
        witness,
        &polynomial,
    );

    let first_folding_factor = recursion_config_builder.folding_factor.at_round(0);

    // to align the first merkle leaves (in base field) (required to appropriately call the precompile multilinear_eval)
    let mut proof_data_padding = (1 << first_folding_factor)
        - ((PUBLIC_INPUT_START
            + public_input.len()
            + {
                // sumcheck polys
                first_folding_factor * 3 * VECTOR_LEN
            }
            + {
                // merkle root
                VECTOR_LEN
            }
            + {
                // grinding witness
                VECTOR_LEN
            }
            + {
                // ood answer
                VECTOR_LEN
            })
            % (1 << first_folding_factor));
    assert_eq!(proof_data_padding % 8, 0);
    proof_data_padding /= 8;
    program_str = program_str
        .replace(
            "PADDING_FOR_INITIAL_MERKLE_LEAVES_PLACEHOLDER",
            &proof_data_padding.to_string(),
        )
        .replace("N_VARS_PLACEHOLDER", &NUM_VARIABLES.to_string())
        .replace(
            "LOG_INV_RATE_PLACEHOLDER",
            &recursion_config_builder.starting_log_inv_rate.to_string(),
        );

    public_input.extend(F::zero_vec(proof_data_padding * 8));

    public_input.extend(prover_state.proof_data()[commitment_size..].to_vec());

    // Reconstruct verifier's view of the transcript using the DomainSeparator and prover's data
    let mut verifier_state = build_verifier_state(&prover_state);

    // Parse the commitment
    let parsed_commitment = recursion_config
        .parse_commitment(&mut verifier_state)
        .unwrap();

    recursion_config
        .verify(&mut verifier_state, &parsed_commitment, statement)
        .unwrap();

    // #[rustfmt::skip] // debug
    // std::fs::write("public_input.txt", build_public_memory(&public_input).chunks_exact(8).enumerate().map(|(i, chunk)| { format!("{} - {}: {}\n", i, i * 8, chunk.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(", ")) }).collect::<String>(),).unwrap();

    // utils::init_tracing();
    let (bytecode, function_locations) = compile_program(&program_str);
    let time = Instant::now();
    let (proof_data, proof_size) = prove_execution(
        &bytecode,
        &program_str,
        &function_locations,
        &public_input,
        &[],
        whir_config_builder(),
        false,
    );
    let proving_time = time.elapsed();
    verify_execution(&bytecode, &public_input, proof_data, whir_config_builder()).unwrap();
    RecursionBenchStats {
        proving_time,
        proof_size,
    }
}

pub fn bench_recursion() -> Duration {
    run_recursion_benchmark().proving_time
}

#[test]
fn test_whir_recursion() {
    let stats = run_recursion_benchmark();
    println!(
        "\nWHIR recursion, proving time: {:?}, proof size: {} KiB (not optimized)",
        stats.proving_time,
        stats.proof_size * F::bits() / (8 * 1024)
    );
}
