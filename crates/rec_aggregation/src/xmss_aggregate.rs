use lean_compiler::*;
use lean_prover::{prove_execution::prove_execution, verify_execution::verify_execution};
use lean_vm::*;
use leansig::signature::SignatureScheme;
use leansig::signature::SignatureSchemeSecretKey;
use leansig::symmetric::message_hash::MessageHash;
use leansig::symmetric::tweak_hash::poseidon::PoseidonTweak;
use multilinear_toolkit::prelude::*;
use rand::{Rng, SeedableRng, rngs::StdRng};
use serde::{Deserialize, Serialize};
use std::sync::OnceLock;
use std::time::Instant;
use std::{mem::transmute, path::Path};
use tracing::{info_span, instrument};
use whir_p3::precompute_dft_twiddles;

#[cfg(feature = "test_config")]
pub use crate::wrappers::test_config as config;

#[cfg(not(feature = "test_config"))]
pub use crate::wrappers::prod_config as config;

use config::{
    BASE, CAPACITY, DIMENSION, HASH_LEN_FE, IS_PROD_CONFIG, LOG_LIFETIME, LeanSigPubKey, LeanSigScheme,
    LeanSigSignature, MH, PARAMETER_LEN, RAND_LEN_FE, TWEAK_LEN_FE,
};

static XMSS_AGGREGATION_PROGRAM: OnceLock<Bytecode> = OnceLock::new();

fn get_xmss_aggregation_program() -> &'static Bytecode {
    XMSS_AGGREGATION_PROGRAM.get_or_init(compile_xmss_aggregation_program)
}

pub fn xmss_setup_aggregation_program() {
    let _ = get_xmss_aggregation_program();
}

fn build_public_input(
    pub_keys: &[LeanSigPubKey],
    encoding_randomness: &[[F; RAND_LEN_FE]],
    message: &[u8; 32],
    epoch: u32,
) -> Vec<F> {
    assert_eq!(pub_keys.len(), encoding_randomness.len());
    let mut public_input = vec![F::from_usize(pub_keys.len())];
    for chain_index in 0..DIMENSION as u8 {
        for pos_in_chain in 1..BASE as u8 {
            let chain_tweak = PoseidonTweak::ChainTweak {
                epoch,
                chain_index,
                pos_in_chain,
            }
            .to_field_elements::<TWEAK_LEN_FE>();
            public_input.extend(unsafe { transmute::<_, [F; TWEAK_LEN_FE]>(chain_tweak) });
        }
    }
    let mut pos_in_level = epoch;
    for level in 0..=LeanSigScheme::LIFETIME.ilog2() as u8 {
        let tree_tweak = PoseidonTweak::TreeTweak { pos_in_level, level }.to_field_elements::<TWEAK_LEN_FE>();
        public_input.extend(unsafe { transmute::<_, [F; TWEAK_LEN_FE]>(tree_tweak) });
        public_input.push(F::from_u32((!pos_in_level) & 1));
        pos_in_level >>= 1;
    }

    for (pub_key, randomness) in pub_keys.iter().zip(encoding_randomness.iter()) {
        let encoding = MH::apply(pub_key.parameter(), epoch, unsafe { transmute(randomness) }, message);
        assert_eq!(encoding.len(), DIMENSION);
        let merkle_root = unsafe { transmute::<_, Vec<F>>(pub_key.root().to_vec()) };
        let public_param = unsafe { transmute::<_, Vec<F>>(pub_key.parameter().to_vec()) };

        public_input.extend(merkle_root);
        public_input.extend(public_param);
        public_input.extend(encoding.iter().map(|&x| F::from_u8(x)));
    }
    public_input
}

fn build_private_input(all_signatures: &[LeanSigSignature]) -> Vec<F> {
    let mut private_input = Vec::<F>::new();
    for signature in all_signatures {
        let chain_tips = unsafe { transmute::<_, Vec<[F; HASH_LEN_FE]>>(signature.hashes().clone()) };
        let merkle_path = unsafe { transmute::<_, Vec<[F; HASH_LEN_FE]>>(signature.path().clone()) };
        assert_eq!(merkle_path.len(), LeanSigScheme::LIFETIME.ilog2() as usize);
        private_input.extend(chain_tips.into_iter().flatten());
        private_input.extend(merkle_path.into_iter().flatten());
    }
    private_input
}

#[instrument(skip_all)]
fn compile_xmss_aggregation_program() -> Bytecode {
    let src_file = Path::new(env!("CARGO_MANIFEST_DIR")).join("xmss_aggregate.lean_lang");
    let merkle_leaf_len_fe = PARAMETER_LEN + TWEAK_LEN_FE + DIMENSION * HASH_LEN_FE;
    let sponge_rate_fe = 24 - CAPACITY;
    let sponge_n_perms = merkle_leaf_len_fe.div_ceil(sponge_rate_fe);
    let sponge_final_zero_padding = (sponge_n_perms * sponge_rate_fe) - merkle_leaf_len_fe;
    let sponge_capacity = if IS_PROD_CONFIG {
        vec![
            287609684, 1664498138, 719484663, 1366363664, 1775736341, 1392984152, 1281304957, 1948506587, 660369959,
        ]
    } else {
        vec![
            1665285720, 695566739, 283798675, 1389712078, 1693509235, 1598839968, 1965072165, 1925594806, 1228158567,
        ]
    };
    let mut program_str = std::fs::read_to_string(src_file)
        .unwrap()
        .replace("W_PLACEHOLDER", &BASE.to_string())
        .replace("LOG_LIFETIME_PLACEHOLDER", &LOG_LIFETIME.to_string())
        .replace("SPONGE_N_PERMS_PLACEHOLDER", &sponge_n_perms.to_string())
        .replace(
            "SPONGE_FINAL_ZERO_PADDING_PLACEHOLDER",
            &sponge_final_zero_padding.to_string(),
        )
        .replace("V_PLACEHOLDER", &DIMENSION.to_string());
    for (i, cap) in sponge_capacity.iter().enumerate() {
        program_str = program_str.replace(&format!("CAP_{}_PLACEHOLDER", i), &cap.to_string());
    }
    compile_program(program_str)
}

pub fn gen_pubkey_and_signature(
    log_lifetime: u32,
    activation_epoch: u32,
    epoch: u32,
    message: &[u8; 32],
) -> (LeanSigPubKey, LeanSigSignature) {
    let lifetime = 1 << log_lifetime;
    let mut rng = StdRng::seed_from_u64(0);
    let (pk, mut sk) = LeanSigScheme::key_gen(&mut rng, activation_epoch as usize, lifetime as usize);
    let mut iterations = 0;
    while !sk.get_prepared_interval().contains(&(epoch as u64)) && iterations < epoch {
        sk.advance_preparation();
        iterations += 1;
    }
    let sig = LeanSigScheme::sign(&sk, epoch, message).unwrap();
    assert!(LeanSigScheme::verify(&pk, epoch, message, &sig));

    (pk, sig)
}

pub fn run_xmss_benchmark(n_xmss: usize, tracing: bool) {
    if tracing {
        utils::init_tracing();
    }
    xmss_setup_aggregation_program();
    precompute_dft_twiddles::<F>(1 << 24);

    let mut rng = StdRng::seed_from_u64(0);
    let message: [u8; 32] = rng.random();
    let epoch: u32 = 11;

    let lifetime_range = if IS_PROD_CONFIG { 5..10 } else { 3..7 };
    let log_lifetimes = (0..n_xmss)
        .map(|_| rng.random_range(lifetime_range.clone()))
        .collect::<Vec<u32>>();

    let mut pub_keys = Vec::new();
    let mut signatures = Vec::new();
    for &log_lifetime in &log_lifetimes {
        let activation_epoch = epoch - log_lifetime;

        let file_name = format!(
            "xmss_example_{}_{}_{}_{}_{}.bin",
            IS_PROD_CONFIG,
            log_lifetime,
            activation_epoch,
            epoch,
            hex::encode(message)
        );
        let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("test_data").join(file_name);
        if path.exists() {
            let data = std::fs::read(&path).unwrap();
            let (pk, sig): (LeanSigPubKey, LeanSigSignature) = bincode::deserialize(&data).unwrap();
            pub_keys.push(pk);
            signatures.push(sig);
        } else {
            println!(
                "Generating XMSS keypair and signature for log_lifetime = {}",
                log_lifetime
            );
            let (pk, sig) = gen_pubkey_and_signature(log_lifetime, activation_epoch, epoch, &message);
            let data = bincode::serialize(&(pk.clone(), sig.clone())).unwrap();
            std::fs::create_dir_all(path.parent().unwrap()).unwrap();
            std::fs::write(&path, &data).unwrap();
            pub_keys.push(pk);
            signatures.push(sig);
        }
    }

    let time = Instant::now();
    let (proof_data, n_field_elements_in_proof, summary) =
        xmss_aggregate_signatures_helper(&pub_keys, &signatures, &message, epoch).unwrap();
    let proving_time = time.elapsed();

    xmss_verify_aggregated_signatures(&pub_keys, &message, &proof_data, epoch).unwrap();

    println!("{summary}");
    println!(
        "XMSS aggregation, proving time: {:.3} s ({:.1} XMSS/s), snark proof size: {} KiB (not optimized)",
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
    pub_keys: &[LeanSigPubKey],
    signatures: &[LeanSigSignature],
    message: &[u8; 32],
    epoch: u32,
) -> Result<Devnet2XmssAggregateSignature, XmssAggregateError> {
    Ok(xmss_aggregate_signatures_helper(pub_keys, signatures, message, epoch)?.0)
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Devnet2XmssAggregateSignature {
    pub proof_bytes: Vec<u8>,
    pub encoding_randomness: Vec<[F; RAND_LEN_FE]>,
}

fn xmss_aggregate_signatures_helper(
    pub_keys: &[LeanSigPubKey],
    signatures: &[LeanSigSignature],
    message: &[u8; 32],
    epoch: u32,
) -> Result<(Devnet2XmssAggregateSignature, usize, String), XmssAggregateError> {
    if pub_keys.len() != signatures.len() {
        return Err(XmssAggregateError::WrongSignatureCount);
    }

    let program = get_xmss_aggregation_program();

    // let poseidons_16_precomputed = precompute_poseidons(xmss_pub_keys, all_signatures, &message_hash)
    //     .ok_or(XmssAggregateError::InvalidSigature)?;
    tracing::warn!("TODO precompute poseidons in parallel + SIMD");

    let encoding_randomness: Vec<[F; RAND_LEN_FE]> = signatures
        .iter()
        .map(|sig| unsafe { transmute::<_, [F; RAND_LEN_FE]>(*sig.rho()) })
        .collect();
    let public_input = build_public_input(pub_keys, &encoding_randomness, message, epoch);
    let private_input = build_private_input(signatures);

    let (proof, summary) = prove_execution(
        program,
        (&public_input, &private_input),
        false,
        &vec![], // TODO
        &vec![], // TODO
    );

    let proof_bytes = info_span!("Proof serialization").in_scope(|| bincode::serialize(&proof).unwrap());

    let final_proof = Devnet2XmssAggregateSignature {
        proof_bytes,
        encoding_randomness,
    };

    Ok((final_proof, proof.proof_size, summary))
}

pub fn xmss_verify_aggregated_signatures(
    pub_keys: &[LeanSigPubKey],
    message: &[u8; 32],
    agg_signature: &Devnet2XmssAggregateSignature,
    epoch: u32,
) -> Result<(), ProofError> {
    let program = get_xmss_aggregation_program();

    let proof = info_span!("Proof deserialization")
        .in_scope(|| bincode::deserialize(&agg_signature.proof_bytes))
        .map_err(|_| ProofError::InvalidProof)?;

    let public_input = build_public_input(pub_keys, &agg_signature.encoding_randomness, message, epoch);

    verify_execution(program, &public_input, proof)
}

#[test]
fn test_xmss_aggregate() {
    run_xmss_benchmark(3, false);
}
