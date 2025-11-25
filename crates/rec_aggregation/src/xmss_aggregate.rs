use lean_compiler::*;
use lean_prover::{LOG_SMALLEST_DECOMPOSITION_CHUNK, whir_config_builder};
use lean_prover::{prove_execution::prove_execution, verify_execution::verify_execution};
use lean_vm::*;
use multilinear_toolkit::prelude::*;
use rand::{Rng, SeedableRng, rngs::StdRng};
use std::path::Path;
use std::time::Instant;
use tracing::instrument;
use whir_p3::precompute_dft_twiddles;
use xmss::{
    MAX_LOG_LIFETIME, Poseidon16History, Poseidon24History, V, XmssPublicKey, XmssSignature,
    generate_phony_xmss_signatures,
};

const XMSS_SIG_SIZE_VEC_PADDED: usize = (V + 1 + MAX_LOG_LIFETIME) + MAX_LOG_LIFETIME.div_ceil(8);

fn build_public_input(xmss_pub_keys: &[XmssPublicKey], message_hash: [F; 8]) -> Vec<F> {
    let mut public_input = message_hash.to_vec();
    public_input.extend(xmss_pub_keys.iter().flat_map(|pk| pk.merkle_root));
    public_input.extend(xmss_pub_keys.iter().map(|pk| F::from_usize(pk.log_lifetime)));
    public_input.extend(F::zero_vec(
        xmss_pub_keys.len().next_multiple_of(8) - xmss_pub_keys.len(),
    ));

    let min_public_input_size = (1 << LOG_SMALLEST_DECOMPOSITION_CHUNK) - NONRESERVED_PROGRAM_INPUT_START;
    public_input.extend(F::zero_vec(min_public_input_size.saturating_sub(public_input.len())));
    let private_input_start =
        F::from_usize((public_input.len() + 8 + NONRESERVED_PROGRAM_INPUT_START).next_power_of_two());
    public_input.splice(
        0..0,
        [
            vec![
                private_input_start,
                F::from_usize(xmss_pub_keys.len()),
                F::from_usize(XMSS_SIG_SIZE_VEC_PADDED),
            ],
            vec![F::ZERO; 5],
        ]
        .concat(),
    );
    public_input
}

fn build_private_input(all_signatures: &[XmssSignature], xmss_pub_keys: &[XmssPublicKey]) -> Vec<F> {
    let mut private_input = vec![];
    for (signature, pubkey) in all_signatures.iter().zip(xmss_pub_keys) {
        let initial_private_input_len = private_input.len();
        private_input.extend(signature.wots_signature.randomness.to_vec());
        private_input.extend(
            signature
                .wots_signature
                .chain_tips
                .iter()
                .flat_map(|digest| digest.to_vec()),
        );
        private_input.extend(signature.merkle_proof.iter().copied().flatten());
        let wots_index = signature.slot.checked_sub(pubkey.first_slot).unwrap();
        private_input.extend((0..pubkey.log_lifetime).map(|i| {
            if (wots_index >> i).is_multiple_of(2) {
                F::ONE
            } else {
                F::ZERO
            }
        }));
        let sig_size = private_input.len() - initial_private_input_len;
        private_input.extend(F::zero_vec(XMSS_SIG_SIZE_VEC_PADDED * VECTOR_LEN - sig_size));
    }
    private_input
}

#[derive(Debug, Clone)]
pub struct XmssAggregationProgram {
    pub bytecode: Bytecode,
    pub default_no_vec_mem: usize,
    pub no_vec_mem_per_log_lifetime: Vec<usize>,
}

impl XmssAggregationProgram {
    pub fn compute_non_vec_memory(&self, log_lifetimes: &[usize]) -> usize {
        log_lifetimes
            .iter()
            .map(|&ll| self.no_vec_mem_per_log_lifetime[ll - 1])
            .sum::<usize>()
            + self.default_no_vec_mem
    }
}

#[instrument(skip_all)]
pub fn compile_xmss_aggregation_program() -> XmssAggregationProgram {
    let src_file = Path::new(env!("CARGO_MANIFEST_DIR")).join("xmss_aggregate.lean_lang");
    let program_str = std::fs::read_to_string(src_file).unwrap();
    let bytecode = compile_program(program_str);
    let default_no_vec_mem = exec_phony_xmss(&bytecode, &[]).no_vec_runtime_memory;
    let mut no_vec_mem_per_log_lifetime = vec![];
    for log_lifetime in 1..=MAX_LOG_LIFETIME {
        let no_vec_mem = exec_phony_xmss(&bytecode, &[log_lifetime]).no_vec_runtime_memory;
        no_vec_mem_per_log_lifetime.push(no_vec_mem.checked_sub(default_no_vec_mem).unwrap());
    }

    let res = XmssAggregationProgram {
        bytecode,
        default_no_vec_mem,
        no_vec_mem_per_log_lifetime,
    };

    let n_sanity_checks = 50;
    let mut rng = rand::rng();
    for _ in 0..n_sanity_checks {
        let n_sigs = rng.random_range(1..=25);
        let log_lifetimes = (0..n_sigs)
            .map(|_| rng.random_range(1..=MAX_LOG_LIFETIME))
            .collect::<Vec<_>>();
        let result = exec_phony_xmss(&res.bytecode, &log_lifetimes);
        assert_eq!(
            result.no_vec_runtime_memory,
            res.compute_non_vec_memory(&log_lifetimes),
            "inconsistent no-vec memory for log_lifetimes : {:?}: non linear formula, TODO",
            log_lifetimes
        );
    }
    res
}

fn exec_phony_xmss(bytecode: &Bytecode, log_lifetimes: &[usize]) -> ExecutionResult {
    let mut rng = StdRng::seed_from_u64(0);
    let message_hash: [F; 8] = rng.random();
    let first_slot = 1111;
    let (xmss_pub_keys, all_signatures) = generate_phony_xmss_signatures(&log_lifetimes, message_hash, first_slot);
    let public_input = build_public_input(&xmss_pub_keys, message_hash);
    let private_input = build_private_input(&all_signatures, &xmss_pub_keys);
    execute_bytecode(
        &bytecode,
        (&public_input, &private_input),
        1 << 21,
        false,
        (&vec![], &vec![]),
    )
}

pub fn run_xmss_benchmark(log_lifetimes: &[usize]) {
    utils::init_tracing();

    let program = compile_xmss_aggregation_program();

    let mut rng = StdRng::seed_from_u64(0);
    let message_hash: [F; 8] = rng.random();
    let first_slot = 785555;

    let (xmss_pub_keys, all_signatures) = generate_phony_xmss_signatures(&log_lifetimes, message_hash, first_slot);

    let public_input = build_public_input(&xmss_pub_keys, message_hash);
    let private_input = build_private_input(&all_signatures, &xmss_pub_keys);

    precompute_dft_twiddles::<F>(1 << 24);

    let time = Instant::now();

    let (poseidons_16_precomputed, poseidons_24_precomputed) =
        precompute_poseidons(&xmss_pub_keys, &all_signatures, &message_hash);

    let (proof_data, proof_size, summary) = prove_execution(
        &program.bytecode,
        (&public_input, &private_input),
        whir_config_builder(),
        program.compute_non_vec_memory(&log_lifetimes),
        false,
        (&poseidons_16_precomputed, &poseidons_24_precomputed),
    );
    let proving_time = time.elapsed();

    verify_execution(&program.bytecode, &public_input, proof_data, whir_config_builder()).unwrap();

    println!("{summary}");
    println!(
        "XMSS aggregation, proving time: {:.3} s ({:.1} XMSS/s), proof size: {} KiB (not optimized)",
        proving_time.as_secs_f64(),
        log_lifetimes.len() as f64 / proving_time.as_secs_f64(),
        proof_size * F::bits() / (8 * 1024)
    );
}

#[instrument(skip_all)]
fn precompute_poseidons(
    xmss_pub_keys: &[XmssPublicKey],
    all_signatures: &[XmssSignature],
    message_hash: &[F; 8],
) -> (Poseidon16History, Poseidon24History) {
    assert_eq!(xmss_pub_keys.len(), all_signatures.len());
    let (poseidon_16_traces, poseidon_24_traces): (Vec<_>, Vec<_>) = xmss_pub_keys
        .par_iter()
        .zip(all_signatures.par_iter())
        .map(|(pub_key, sig)| pub_key.verify_with_poseidon_trace(message_hash, sig).unwrap())
        .unzip();
    (
        poseidon_16_traces.into_par_iter().flatten().collect(),
        poseidon_24_traces.into_par_iter().flatten().collect(),
    )
}

#[test]
fn test_xmss_aggregate() {
    let n_xmss = 50;
    let mut rng = StdRng::seed_from_u64(0);
    let log_lifetimes = (0..n_xmss)
        .map(|_| rng.random_range(1..=MAX_LOG_LIFETIME))
        .collect::<Vec<_>>();
    run_xmss_benchmark(&log_lifetimes);
}
