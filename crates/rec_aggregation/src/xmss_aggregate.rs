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
use xmss::{Poseidon16History, Poseidon24History, V, XmssPublicKey, XmssSignature, generate_phony_xmss_signatures};

const MAX_LOG_LIFETIME: usize = 30;

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
    public_input.insert(
        0,
        F::from_usize((public_input.len() + 8 + NONRESERVED_PROGRAM_INPUT_START).next_power_of_two()),
    );
    public_input.splice(1..1, F::zero_vec(7));
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

pub fn run_xmss_benchmark(n_xmss: usize) {
    let src_file = Path::new(env!("CARGO_MANIFEST_DIR")).join("xmss_aggregate.lean_lang");
    let mut program_str = std::fs::read_to_string(src_file).unwrap();

    program_str = program_str
        .replace("N_PUBLIC_KEYS_PLACE_HOLDER", &n_xmss.to_string())
        .replace("XMSS_SIG_SIZE_PLACE_HOLDER", &XMSS_SIG_SIZE_VEC_PADDED.to_string());

    let mut rng = StdRng::seed_from_u64(0);
    let message_hash: [F; 8] = rng.random();
    let first_slot = 785555;

    let log_lifetimes = (0..n_xmss)
        .map(|_| rng.random_range(MAX_LOG_LIFETIME - 3..=MAX_LOG_LIFETIME))
        .collect::<Vec<_>>();

    let (xmss_pub_keys, all_signatures) = generate_phony_xmss_signatures(&log_lifetimes, message_hash, first_slot);

    let bytecode = compile_program(program_str);

    let public_input = build_public_input(&xmss_pub_keys, message_hash);
    let private_input = build_private_input(&all_signatures, &xmss_pub_keys);

    // in practice we will precompute all the possible values
    // (depending on the number of recursions + the number of xmss signatures)
    // (or even better: find a linear relation)
    let no_vec_runtime_memory = execute_bytecode(
        &bytecode,
        (&public_input, &private_input),
        1 << 21,
        false,
        (&vec![], &vec![]),
    )
    .no_vec_runtime_memory;

    utils::init_tracing();

    precompute_dft_twiddles::<F>(1 << 24);

    let time = Instant::now();

    let (poseidons_16_precomputed, poseidons_24_precomputed) =
        precompute_poseidons(&xmss_pub_keys, &all_signatures, &message_hash);

    let (proof_data, proof_size, summary) = prove_execution(
        &bytecode,
        (&public_input, &private_input),
        whir_config_builder(),
        no_vec_runtime_memory,
        false,
        (&poseidons_16_precomputed, &poseidons_24_precomputed),
    );
    let proving_time = time.elapsed();
    verify_execution(&bytecode, &public_input, proof_data, whir_config_builder()).unwrap();

    println!("{summary}");
    println!(
        "XMSS aggregation, proving time: {:.3} s ({:.1} XMSS/s), proof size: {} KiB (not optimized)",
        proving_time.as_secs_f64(),
        n_xmss as f64 / proving_time.as_secs_f64(),
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
    let n_xmss: usize = std::env::var("NUM_XMSS_AGGREGATED")
        .unwrap_or("100".to_string())
        .parse()
        .unwrap();
    run_xmss_benchmark(n_xmss);
}
