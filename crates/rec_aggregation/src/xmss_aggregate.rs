use lean_compiler::*;
use lean_prover::{default_whir_config, prove_execution::prove_execution, verify_execution::verify_execution};
use lean_vm::*;
use multilinear_toolkit::prelude::*;
use rand::{Rng, SeedableRng, rngs::StdRng};
use std::sync::OnceLock;
use std::time::Instant;
use std::{collections::BTreeMap, path::Path};
use tracing::{info_span, instrument};
use xmss::{
    LOG_LIFETIME, MESSAGE_LEN_FE, Poseidon16History, RANDOMNESS_LEN_FE, SIG_SIZE_FE, TARGET_SUM, V, V_GRINDING, W, XmssPublicKey, XmssSignature, slot_to_field_elements, xmss_verify_with_poseidon_trace
};

static XMSS_AGGREGATION_PROGRAM: OnceLock<Bytecode> = OnceLock::new();
const LOG_INV_RATE: usize = 1;

fn get_xmss_aggregation_program() -> &'static Bytecode {
    XMSS_AGGREGATION_PROGRAM.get_or_init(compile_xmss_aggregation_program)
}

pub fn xmss_setup_aggregation_program() {
    let _ = get_xmss_aggregation_program();
}

fn build_public_input(xmss_pub_keys: &[XmssPublicKey], message: [F; MESSAGE_LEN_FE], slot: u32) -> Vec<F> {
    let mut public_input = vec![];
    public_input.push(F::ZERO); // private input start, filled later
    public_input.push(F::from_usize(xmss_pub_keys.len()));
    public_input.extend(message.to_vec());
    let [slot_lo, slot_hi] = slot_to_field_elements(slot);
    public_input.push(slot_lo);
    public_input.push(slot_hi);
    for level in 0..LOG_LIFETIME {
        let is_left = (((slot as u64) >> level) & 1) == 0;
        public_input.push(F::from_usize(is_left as usize));
    }
    public_input.extend(xmss_pub_keys.iter().flat_map(|pk| pk.merkle_root));
    let private_input_start = (NONRESERVED_PROGRAM_INPUT_START + public_input.len()).next_power_of_two();
    public_input[0] = F::from_usize(private_input_start);
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
        assert_eq!(sig_size, SIG_SIZE_FE);
    }
    private_input
}

#[instrument(skip_all)]
fn compile_xmss_aggregation_program() -> Bytecode {
    let filepath = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("xmss_aggregate.py")
        .to_str()
        .unwrap()
        .to_string();
    let mut replacements = BTreeMap::new();
    replacements.insert("V_PLACEHOLDER".to_string(), V.to_string());
    replacements.insert("V_GRINDING_PLACEHOLDER".to_string(), V_GRINDING.to_string());
    replacements.insert("W_PLACEHOLDER".to_string(), W.to_string());
    replacements.insert("TARGET_SUM_PLACEHOLDER".to_string(), TARGET_SUM.to_string());
    replacements.insert("LOG_LIFETIME_PLACEHOLDER".to_string(), LOG_LIFETIME.to_string());
    replacements.insert("MESSAGE_LEN_PLACEHOLDER".to_string(), MESSAGE_LEN_FE.to_string());
    replacements.insert("RANDOMNESS_LEN_PLACEHOLDER".to_string(), RANDOMNESS_LEN_FE.to_string());
    compile_program_with_flags(&ProgramSource::Filepath(filepath), CompilationFlags { replacements })
}

pub fn run_xmss_benchmark(n_signatures: usize, tracing: bool) {
    if tracing {
        utils::init_tracing();
    }
    xmss_setup_aggregation_program();
    precompute_dft_twiddles::<F>(1 << 24);

    let message = (0..MESSAGE_LEN_FE)
        .map(|i| F::from_usize(i))
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();
    let slot = 1111;

    let pub_keys_and_sigs = (0..n_signatures)
        .into_par_iter()
        .map(|i| {
            let mut rng = StdRng::seed_from_u64(i as u64);
            let start = slot - rng.random_range(0..5);
            let end = slot + rng.random_range(1..5);
            let (sk, pk) = xmss::xmss_key_gen(rng.random(), start, end).unwrap();
            let sig = xmss::xmss_sign(&mut rng, &sk, &message, slot).unwrap();
            (pk, sig)
        })
        .collect::<Vec<_>>();
    let (xmss_pub_keys, all_signatures): (Vec<_>, Vec<_>) = pub_keys_and_sigs.into_iter().unzip();
    let time = Instant::now();
    let (proof_data, n_field_elements_in_proof, summary) =
        xmss_aggregate_signatures_helper(&xmss_pub_keys, &all_signatures, message, slot).unwrap();
    let proving_time = time.elapsed();

    xmss_verify_aggregated_signatures(&xmss_pub_keys, message, &proof_data, slot).unwrap();

    println!("{summary}");
    println!(
        "XMSS aggregation, proving time: {:.3} s ({:.1} XMSS/s), proof size: {} KiB",
        proving_time.as_secs_f64(),
        n_signatures as f64 / proving_time.as_secs_f64(),
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
    message: [F; MESSAGE_LEN_FE],
    slot: u32,
) -> Result<Vec<u8>, XmssAggregateError> {
    Ok(xmss_aggregate_signatures_helper(xmss_pub_keys, all_signatures, message, slot)?.0)
}

fn xmss_aggregate_signatures_helper(
    xmss_pub_keys: &[XmssPublicKey],
    all_signatures: &[XmssSignature],
    message: [F; MESSAGE_LEN_FE],
    slot: u32,
) -> Result<(Vec<u8>, usize, String), XmssAggregateError> {
    if xmss_pub_keys.len() != all_signatures.len() {
        return Err(XmssAggregateError::WrongSignatureCount);
    }

    let program = get_xmss_aggregation_program();

    let poseidons_16_precomputed =
        precompute_poseidons(xmss_pub_keys, all_signatures, &message).ok_or(XmssAggregateError::InvalidSigature)?;

    let public_input = build_public_input(xmss_pub_keys, message, slot);
    let private_input = build_private_input(all_signatures);

    let proof = prove_execution(
        program,
        (&public_input, &private_input),
        &poseidons_16_precomputed,
        &default_whir_config(LOG_INV_RATE),
        false,
    );

    let proof_bytes = info_span!("Proof serialization").in_scope(|| bincode::serialize(&proof.proof).unwrap());

    Ok((proof_bytes, proof.proof_size_fe, proof.exec_summary))
}

pub fn xmss_verify_aggregated_signatures(
    xmss_pub_keys: &[XmssPublicKey],
    message: [F; MESSAGE_LEN_FE],
    proof_bytes: &[u8],
    slot: u32,
) -> Result<(), ProofError> {
    let program = get_xmss_aggregation_program();

    let proof = info_span!("Proof deserialization")
        .in_scope(|| bincode::deserialize(proof_bytes))
        .map_err(|_| ProofError::InvalidProof)?;

    let public_input = build_public_input(xmss_pub_keys, message, slot);

    verify_execution(program, &public_input, proof, &default_whir_config(LOG_INV_RATE)).map(|_| ())
}

#[instrument(skip_all)]
fn precompute_poseidons(
    xmss_pub_keys: &[XmssPublicKey],
    all_signatures: &[XmssSignature],
    message: &[F; MESSAGE_LEN_FE],
) -> Option<Poseidon16History> {
    assert_eq!(xmss_pub_keys.len(), all_signatures.len());
    let traces = xmss_pub_keys
        .par_iter()
        .zip(all_signatures.par_iter())
        .map(|(pub_key, sig)| xmss_verify_with_poseidon_trace(pub_key, message, sig))
        .collect::<Result<Vec<_>, _>>()
        .ok()?;
    Some(traces.into_par_iter().flatten().collect())
}

#[test]
fn test_xmss_aggregate() {
    run_xmss_benchmark(1, false);
}
