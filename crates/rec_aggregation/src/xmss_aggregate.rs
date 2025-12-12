use lean_compiler::*;
use lean_prover::{prove_execution::prove_execution, verify_execution::verify_execution};
use lean_vm::*;
use leansig::signature::generalized_xmss::instantiations_poseidon_top_level::lifetime_2_to_the_32::hashing_optimized as leansig_module;
use leansig::signature::{SignatureScheme, SignatureSchemeSecretKey};
use leansig::symmetric::message_hash::MessageHash;
use leansig::symmetric::tweak_hash::poseidon::PoseidonTweak;
use leansig_module::{HASH_LEN_FE, MH, RAND_LEN_FE, TWEAK_LEN_FE};
use multilinear_toolkit::prelude::*;
use rand::{Rng, SeedableRng, rngs::StdRng};
use std::sync::OnceLock;
use std::time::Instant;
use std::{mem::transmute, path::Path};
use tracing::{info_span, instrument};
use whir_p3::precompute_dft_twiddles;

pub type LeanSigScheme = leansig_module::SIGTopLevelTargetSumLifetime32Dim64Base8;
pub type LeanSigPubKey = leansig_module::PubKeyTopLevelTargetSumLifetime32Dim64Base8;
pub type LeanSigSignature = leansig_module::SigTopLevelTargetSumLifetime32Dim64Base8;

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
    for chain_index in 0..MH::DIMENSION as u8 {
        for pos_in_chain in 1..MH::BASE as u8 {
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
        let encoding = MH::apply(&pub_key.parameter, epoch, unsafe { transmute(randomness) }, message);
        assert_eq!(encoding.len(), MH::DIMENSION);
        assert_eq!(MH::DIMENSION, 64); // TODO remove this later
        let merkle_root = unsafe { transmute::<_, Vec<F>>(pub_key.root.to_vec()) };
        assert_eq!(merkle_root.len(), 8);
        let public_param = unsafe { transmute::<_, Vec<F>>(pub_key.parameter.to_vec()) };
        assert_eq!(public_param.len(), 5);

        dbg!(&merkle_root);

        public_input.extend(merkle_root);
        public_input.extend(public_param);
        public_input.extend(encoding.iter().map(|&x| F::from_u8(x)));
    }
    public_input
}

fn build_private_input(all_signatures: &[LeanSigSignature]) -> Vec<F> {
    let mut private_input = Vec::<F>::new();
    for signature in all_signatures {
        let chain_tips = unsafe { transmute::<_, Vec<[F; HASH_LEN_FE]>>(signature.hashes.clone()) };
        let merkle_path = unsafe { transmute::<_, Vec<[F; HASH_LEN_FE]>>(signature.path.clone()) };
        assert_eq!(chain_tips.len(), 64); // TODO remove this later
        assert_eq!(merkle_path.len(), LeanSigScheme::LIFETIME.ilog2() as usize);
        private_input.extend(chain_tips.into_iter().flatten());
        private_input.extend(merkle_path.into_iter().flatten());
    }
    private_input
}

#[instrument(skip_all)]
fn compile_xmss_aggregation_program() -> Bytecode {
    let src_file = Path::new(env!("CARGO_MANIFEST_DIR")).join("xmss_aggregate.lean_lang");
    let program_str = std::fs::read_to_string(src_file).unwrap();
    compile_program(program_str)
}

pub fn run_xmss_benchmark(log_lifetimes: &[usize], tracing: bool) {
    if tracing {
        utils::init_tracing();
    }
    xmss_setup_aggregation_program();
    precompute_dft_twiddles::<F>(1 << 24);

    let mut rng = StdRng::seed_from_u64(0);
    let message: [u8; 32] = rng.random();
    let epoch: u32 = 1000;

    let mut pub_keys = Vec::new();
    let mut signatures = Vec::new();
    for log_lifetime in log_lifetimes {
        let lifetime = 1 << log_lifetime;
        let activation_epoch = epoch.saturating_sub(rng.random_range(0..lifetime - 1));
        let (pk, mut sk) = LeanSigScheme::key_gen(&mut rng, activation_epoch as usize, lifetime as usize);
        let mut iterations = 0;
        while !sk.get_prepared_interval().contains(&(epoch as u64)) && iterations < epoch {
            sk.advance_preparation();
            iterations += 1;
        }
        let sig = LeanSigScheme::sign(&sk, epoch as u32, &message).unwrap();
        dbg!("VERIFYING SIGNATURE");
        assert!(LeanSigScheme::verify(&pk, epoch as u32, &message, &sig));

        pub_keys.push(pk);
        signatures.push(sig);
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

#[derive(Debug, Clone)]
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
        .map(|sig| unsafe { transmute::<_, [F; RAND_LEN_FE]>(sig.rho) })
        .collect();
    let public_input = build_public_input(pub_keys, &encoding_randomness, message, epoch);
    let private_input = build_private_input(signatures);

    let (proof, summary) = prove_execution(
        &program,
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

    verify_execution(&program, &public_input, proof)
}

#[test]
fn test_xmss_aggregate() {
    let n_xmss = 1;
    let mut rng = StdRng::seed_from_u64(0);
    let log_lifetimes = (0..n_xmss).map(|_| rng.random_range(5..10)).collect::<Vec<_>>();
    run_xmss_benchmark(&log_lifetimes, false);
}
