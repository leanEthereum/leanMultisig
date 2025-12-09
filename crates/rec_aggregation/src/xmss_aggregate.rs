use lean_compiler::*;
use lean_prover::{prove_execution::prove_execution, verify_execution::verify_execution};
use lean_vm::*;
use multilinear_toolkit::prelude::*;
use rand::{Rng, SeedableRng, rngs::StdRng};
use std::path::Path;
use std::sync::OnceLock;
use std::time::Instant;
use tracing::{info_span, instrument};
use utils::to_little_endian_in_field;
use whir_p3::precompute_dft_twiddles;
use xmss::{
    Poseidon16History, V, XMSS_MAX_LOG_LIFETIME, XMSS_MIN_LOG_LIFETIME, XmssPublicKey, XmssSignature,
    xmss_generate_phony_signatures, xmss_verify_with_poseidon_trace,
};

static XMSS_AGGREGATION_PROGRAM: OnceLock<XmssAggregationProgram> = OnceLock::new();

fn get_xmss_aggregation_program() -> &'static XmssAggregationProgram {
    XMSS_AGGREGATION_PROGRAM.get_or_init(compile_xmss_aggregation_program)
}

pub fn xmss_setup_aggregation_program() {
    let _ = get_xmss_aggregation_program();
}

fn build_public_input(xmss_pub_keys: &[XmssPublicKey], message_hash: [F; 8], slot: u64) -> Vec<F> {
    let mut public_input = message_hash.to_vec();
    public_input.extend(xmss_pub_keys.iter().flat_map(|pk| pk.merkle_root));
    public_input.extend(xmss_pub_keys.iter().map(|pk| F::from_usize(pk.log_lifetime)));
    for pk in xmss_pub_keys {
        let index_in_merkle_tree = slot.checked_sub(pk.first_slot).unwrap() as usize;
        public_input.extend(to_little_endian_in_field::<F>(
            index_in_merkle_tree,
            XMSS_MAX_LOG_LIFETIME,
        ));
    }
    let mut acc = F::ZERO;
    for pk in xmss_pub_keys {
        public_input.push(acc);
        acc += F::from_usize(1 + V + pk.log_lifetime); // signature size in memory (vectorized)
    }

    public_input.splice(
        0..0,
        [vec![F::from_usize(xmss_pub_keys.len())], vec![F::ZERO; 7]].concat(),
    );
    public_input
}

fn build_private_input(all_signatures: &[XmssSignature]) -> Vec<F> {
    let mut private_input = vec![];
    for signature in all_signatures {
        let initial_private_input_len = private_input.len();
        private_input.extend(signature.wots_signature.randomness.to_vec());
        private_input.extend(
            signature
                .wots_signature
                .chain_tips
                .iter()
                .flat_map(|digest| digest.to_vec()),
        );
        for neighbor in &signature.merkle_proof {
            private_input.extend(neighbor.to_vec());
        }

        let sig_size = private_input.len() - initial_private_input_len;
        assert!(sig_size.is_multiple_of(VECTOR_LEN));
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
            .map(|&ll| self.no_vec_mem_per_log_lifetime[ll - XMSS_MIN_LOG_LIFETIME])
            .sum::<usize>()
            + self.default_no_vec_mem
    }
}

#[instrument(skip_all)]
fn compile_xmss_aggregation_program() -> XmssAggregationProgram {
    let src_file = Path::new(env!("CARGO_MANIFEST_DIR")).join("xmss_aggregate.lean_lang");
    let program_str = std::fs::read_to_string(src_file).unwrap();
    let bytecode = compile_program(program_str);
    let default_no_vec_mem = exec_phony_xmss(&bytecode, &[]).no_vec_runtime_memory;
    let mut no_vec_mem_per_log_lifetime = vec![];
    for log_lifetime in XMSS_MIN_LOG_LIFETIME..=XMSS_MAX_LOG_LIFETIME {
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
            .map(|_| rng.random_range(XMSS_MIN_LOG_LIFETIME..=XMSS_MAX_LOG_LIFETIME))
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
    let slot = 1111;
    let (xmss_pub_keys, all_signatures) = xmss_generate_phony_signatures(log_lifetimes, message_hash, slot);
    let public_input = build_public_input(&xmss_pub_keys, message_hash, slot);
    let private_input = build_private_input(&all_signatures);
    execute_bytecode(bytecode, (&public_input, &private_input), 1 << 21, false, &vec![])
}

pub fn run_xmss_benchmark(log_lifetimes: &[usize], tracing: bool) {
    if tracing {
        utils::init_tracing();
    }
    xmss_setup_aggregation_program();
    precompute_dft_twiddles::<F>(1 << 24);

    let mut rng = StdRng::seed_from_u64(0);
    let message_hash: [F; 8] = rng.random();
    let slot = 1111;

    let (xmss_pub_keys, all_signatures) = xmss_generate_phony_signatures(log_lifetimes, message_hash, slot);

    let time = Instant::now();
    let (proof_data, n_field_elements_in_proof, summary) =
        xmss_aggregate_signatures_helper(&xmss_pub_keys, &all_signatures, message_hash, slot).unwrap();
    let proving_time = time.elapsed();

    xmss_verify_aggregated_signatures(&xmss_pub_keys, message_hash, &proof_data, slot).unwrap();

    println!("{summary}");
    println!(
        "XMSS aggregation, proving time: {:.3} s ({:.1} XMSS/s), proof size: {} KiB (not optimized)",
        proving_time.as_secs_f64(),
        log_lifetimes.len() as f64 / proving_time.as_secs_f64(),
        n_field_elements_in_proof * F::bits() / (8 * 1024)
    );
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum XmssAggregateError {
    WrongSignatureCount,
    InvalidSigature,
}

pub fn xmss_aggregate_signatures(
    xmss_pub_keys: &[XmssPublicKey],
    all_signatures: &[XmssSignature],
    message_hash: [F; 8],
    slot: u64,
) -> Result<Vec<u8>, XmssAggregateError> {
    Ok(xmss_aggregate_signatures_helper(xmss_pub_keys, all_signatures, message_hash, slot)?.0)
}

fn xmss_aggregate_signatures_helper(
    xmss_pub_keys: &[XmssPublicKey],
    all_signatures: &[XmssSignature],
    message_hash: [F; 8],
    slot: u64,
) -> Result<(Vec<u8>, usize, String), XmssAggregateError> {
    if xmss_pub_keys.len() != all_signatures.len() {
        return Err(XmssAggregateError::WrongSignatureCount);
    }

    let program = get_xmss_aggregation_program();

    let poseidons_16_precomputed = precompute_poseidons(xmss_pub_keys, all_signatures, &message_hash)
        .ok_or(XmssAggregateError::InvalidSigature)?;

    let public_input = build_public_input(xmss_pub_keys, message_hash, slot);
    let private_input = build_private_input(all_signatures);

    let (proof, summary) = prove_execution(
        &program.bytecode,
        (&public_input, &private_input),
        program.compute_non_vec_memory(&xmss_pub_keys.iter().map(|pk| pk.log_lifetime).collect::<Vec<_>>()),
        false,
        &poseidons_16_precomputed,
    );

    let proof_bytes = info_span!("Proof serialization").in_scope(|| bincode::serialize(&proof).unwrap());

    Ok((proof_bytes, proof.proof_size, summary))
}

pub fn xmss_verify_aggregated_signatures(
    xmss_pub_keys: &[XmssPublicKey],
    message_hash: [F; 8],
    proof_bytes: &[u8],
    slot: u64,
) -> Result<(), ProofError> {
    let _ = slot; // TODO
    let program = get_xmss_aggregation_program();

    let proof = info_span!("Proof deserialization")
        .in_scope(|| bincode::deserialize(proof_bytes))
        .map_err(|_| ProofError::InvalidProof)?;

    let public_input = build_public_input(xmss_pub_keys, message_hash, slot);

    verify_execution(&program.bytecode, &public_input, proof)
}

#[instrument(skip_all)]
fn precompute_poseidons(
    xmss_pub_keys: &[XmssPublicKey],
    all_signatures: &[XmssSignature],
    message_hash: &[F; 8],
) -> Option<Poseidon16History> {
    assert_eq!(xmss_pub_keys.len(), all_signatures.len());
    let traces = xmss_pub_keys
        .par_iter()
        .zip(all_signatures.par_iter())
        .map(|(pub_key, sig)| xmss_verify_with_poseidon_trace(pub_key, message_hash, sig))
        .collect::<Result<Vec<_>, _>>()
        .ok()?;
    Some(traces.into_par_iter().flatten().collect())
}

#[test]
fn test_xmss_aggregate() {
    let n_xmss = 10;
    let mut rng = StdRng::seed_from_u64(0);
    let log_lifetimes = (0..n_xmss)
        .map(|_| rng.random_range(XMSS_MIN_LOG_LIFETIME..=XMSS_MAX_LOG_LIFETIME))
        .collect::<Vec<_>>();
    run_xmss_benchmark(&log_lifetimes, false);
}
