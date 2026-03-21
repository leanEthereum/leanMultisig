#![cfg_attr(not(test), allow(unused_crate_dependencies))]
use backend::*;
use lean_prover::SNARK_DOMAIN_SEP;
use lean_prover::prove_execution::prove_execution;
use lean_prover::verify_execution::ProofVerificationDetails;
use lean_prover::verify_execution::verify_execution;
use lean_vm::*;
use leansig_wrapper::{
    LOG_LIFETIME, MESSAGE_LEN_FE, SIG_SIZE_FE
};
use tracing::instrument;
use utils::{build_prover_state, get_poseidon16, poseidon_compress_slice, poseidon16_compress_pair};

use serde::{Deserialize, Serialize};
use std::collections::HashSet;

pub use crate::compilation::{get_aggregation_bytecode, init_aggregation_bytecode};

pub mod benchmark;
mod compilation;

const MERKLE_LEVELS_PER_CHUNK_FOR_SLOT: usize = 4;
const N_MERKLE_CHUNKS_FOR_SLOT: usize = LOG_LIFETIME / MERKLE_LEVELS_PER_CHUNK_FOR_SLOT;

#[derive(Debug, Clone)]
pub struct AggregationTopology {
    pub raw_xmss: usize,
    pub children: Vec<AggregationTopology>,
    pub log_inv_rate: usize,
}

pub(crate) fn count_signers(topology: &AggregationTopology, overlap: usize) -> usize {
    let child_count: usize = topology.children.iter().map(|c| count_signers(c, overlap)).sum();
    let n_overlaps = topology.children.len().saturating_sub(1);
    topology.raw_xmss + child_count - overlap * n_overlaps
}

/// Hash pubkeys via Poseidon24 sponge: capacity(9) || root(8) || pp(5) || zeros(2) per key.
pub fn hash_pubkeys(pub_keys: &[XmssPublicKey]) -> [F; DIGEST_LEN] {
    let mut capacity = [F::ZERO; 9];
    for pk in pub_keys {
        let mut input = [F::ZERO; 24];
        input[..9].copy_from_slice(&capacity);
        input[9..17].copy_from_slice(&pk.merkle_root);
        input[17..22].copy_from_slice(&pk.public_param);
        // input[22..24] = zeros (padding)
        capacity = utils::poseidon24_compress(input);
    }
    capacity[..DIGEST_LEN].try_into().unwrap()
}

fn compute_merkle_chunks_for_slot(slot: u32) -> Vec<F> {
    let mut chunks = Vec::with_capacity(N_MERKLE_CHUNKS_FOR_SLOT);
    for chunk_idx in 0..N_MERKLE_CHUNKS_FOR_SLOT {
        let mut nibble_val: usize = 0;
        for bit in 0..4 {
            let level = chunk_idx * 4 + bit;
            let is_left = (((slot as u64) >> level) & 1) == 0;
            if is_left {
                nibble_val |= 1 << bit;
            }
        }
        chunks.push(F::from_usize(nibble_val));
    }
    chunks
}

/// Pre-compute ALL tweaks for a slot: encoding(2) + chain(V*CHAIN_LENGTH*2) + merkle(LOG_LIFETIME*2).
fn compute_all_tweaks_for_slot(slot: u32) -> Vec<F> {
    let n = xmss::TWEAK_LEN + xmss::V * xmss::CHAIN_LENGTH * xmss::TWEAK_LEN + xmss::LOG_LIFETIME * xmss::TWEAK_LEN;
    let mut tweaks = Vec::with_capacity(n);
    // Encoding tweak
    let [t0, t1] = xmss::make_tweak(xmss::TWEAK_TYPE_ENCODING, 0, slot);
    tweaks.extend([t0, t1]);
    // Chain tweaks
    for chain_idx in 0..xmss::V {
        for step in 0..xmss::CHAIN_LENGTH {
            let [t0, t1] = xmss::make_tweak(xmss::TWEAK_TYPE_CHAIN, chain_idx * xmss::CHAIN_LENGTH + step, slot);
            tweaks.extend([t0, t1]);
        }
    }
    // Merkle tweaks
    for level in 0..xmss::LOG_LIFETIME {
        let parent_level = level + 1;
        let parent_index = if parent_level < 32 { slot >> parent_level } else { 0 };
        let [t0, t1] = xmss::make_tweak(xmss::TWEAK_TYPE_MERKLE, parent_level, parent_index);
        tweaks.extend([t0, t1]);
    }
    assert_eq!(tweaks.len(), n);
    tweaks
}

fn build_non_reserved_public_input(
    n_sigs: usize,
    slice_hash: &[F; DIGEST_LEN],
    message: &[F; MESSAGE_LEN_FE],
    slot: u32,
    bytecode_claim_output: &[F],
    bytecode_hash: &[F; DIGEST_LEN],
) -> Vec<F> {
    let mut pi = vec![];
    pi.push(F::from_usize(n_sigs));
    pi.extend_from_slice(slice_hash);
    pi.extend_from_slice(message);
    let [slot_lo, slot_hi] = slot_to_field_elements(slot);
    pi.push(slot_lo);
    pi.push(slot_hi);
    pi.extend(compute_merkle_chunks_for_slot(slot));
    pi.extend(compute_all_tweaks_for_slot(slot));
    pi.extend_from_slice(bytecode_claim_output);
    pi.extend(std::iter::repeat_n(
        F::ZERO,
        bytecode_claim_output.len().next_multiple_of(DIGEST_LEN) - bytecode_claim_output.len(),
    ));
    pi.extend_from_slice(&poseidon16_compress_pair(bytecode_hash, &SNARK_DOMAIN_SEP));
    pi
}

fn encode_xmss_signature(sig: &XmssSignature) -> Vec<F> {
    let mut data = vec![];
    data.extend(sig.wots_signature.randomness.to_vec());
    data.extend(sig.wots_signature.chain_tips.iter().flat_map(|digest| digest.to_vec()));
    for neighbor in &sig.merkle_proof {
        data.extend(neighbor.to_vec());
    }
    assert_eq!(data.len(), SIG_SIZE_FE);
    data
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct AggregatedXMSS {
    pub pub_keys: Vec<XmssPublicKey>,
    pub proof: Proof<F>,
    pub bytecode_point: Option<MultilinearPoint<EF>>,
    // benchmark / debug purpose
    #[serde(skip, default)]
    pub metadata: Option<ExecutionMetadata>,
}

impl AggregatedXMSS {
    pub fn serialize(&self) -> Vec<u8> {
        let encoded = postcard::to_allocvec(self).expect("postcard serialization failed");
        lz4_flex::compress_prepend_size(&encoded)
    }

    pub fn deserialize(bytes: &[u8]) -> Option<Self> {
        let decompressed = lz4_flex::decompress_size_prepended(bytes).ok()?;
        postcard::from_bytes(&decompressed).ok()
    }

    pub fn public_input(&self, message: &[F; MESSAGE_LEN_FE], slot: u32) -> Vec<F> {
        let bytecode = get_aggregation_bytecode();
        let bytecode_point_n_vars = bytecode.log_size() + log2_ceil_usize(N_INSTRUCTION_COLUMNS);
        let bytecode_claim_size = (bytecode_point_n_vars + 1) * DIMENSION;

        let bytecode_claim_output = match &self.bytecode_point {
            Some(point) => {
                let value = bytecode.instructions_multilinear.evaluate(point);
                let mut ef_claim: Vec<EF> = point.0.clone();
                ef_claim.push(value);
                flatten_scalars_to_base::<F, EF>(&ef_claim)
            }
            None => {
                let mut claim = vec![F::ZERO; bytecode_claim_size];
                claim[bytecode_point_n_vars * DIMENSION] = bytecode.instructions_multilinear[0];
                claim
            }
        };
        let bytecode_claim_size_padded = bytecode_claim_size.next_multiple_of(DIGEST_LEN);
        assert_eq!(bytecode_claim_output.len(), bytecode_claim_size);
        // Pad to match the public input layout
        let mut bytecode_claim_output = bytecode_claim_output;
        bytecode_claim_output.resize(bytecode_claim_size_padded, F::ZERO);

        let slice_hash = hash_pubkeys(&self.pub_keys);

        build_non_reserved_public_input(
            self.pub_keys.len(),
            &slice_hash,
            message,
            slot,
            &bytecode_claim_output,
            &bytecode.hash,
        )
    }
}

pub fn xmss_verify_aggregation(
    agg_sig: &AggregatedXMSS,
    message: &[F; MESSAGE_LEN_FE],
    slot: u32,
) -> Result<ProofVerificationDetails, ProofError> {
    if !agg_sig.pub_keys.is_sorted() {
        return Err(ProofError::InvalidProof);
    }
    let public_input = agg_sig.public_input(message, slot);
    let bytecode = get_aggregation_bytecode();
    verify_execution(bytecode, &public_input, agg_sig.proof.clone()).map(|(details, _)| details)
}

/// panics if one of the sub-proof (children) is invalid
#[instrument(skip_all)]
pub fn xmss_aggregate(
    children: &[AggregatedXMSS],
    mut raw_xmss: Vec<(XmssPublicKey, XmssSignature)>,
    message: &[F; MESSAGE_LEN_FE],
    slot: u32,
    log_inv_rate: usize,
) -> AggregatedXMSS {
    raw_xmss.sort_by(|(a, _), (b, _)| a.cmp(b));
    raw_xmss.dedup_by(|(a, _), (b, _)| a.merkle_root == b.merkle_root);

    let n_recursions = children.len();
    let raw_count = raw_xmss.len();
    let whir_config = lean_prover::default_whir_config(log_inv_rate);

    let bytecode = get_aggregation_bytecode();
    let bytecode_point_n_vars = bytecode.log_size() + log2_ceil_usize(N_INSTRUCTION_COLUMNS);
    let bytecode_claim_size = (bytecode_point_n_vars + 1) * DIMENSION;

    // Build global_pub_keys as sorted deduplicated union
    let mut global_pub_keys: Vec<XmssPublicKey> = raw_xmss.iter().map(|(pk, _)| pk.clone()).collect();
    for child in children.iter() {
        assert!(child.pub_keys.is_sorted(), "child pub_keys must be sorted");
        global_pub_keys.extend_from_slice(&child.pub_keys);
    }
    global_pub_keys.sort();
    global_pub_keys.dedup();
    let n_sigs = global_pub_keys.len();

    // Verify child proofs
    let mut child_pub_inputs = vec![];
    let mut child_bytecode_evals = vec![];
    let mut child_raw_proofs = vec![];
    for child in children {
        let child_pub_input = child.public_input(message, slot);
        let (verif, raw_proof) = verify_execution(bytecode, &child_pub_input, child.proof.clone()).unwrap();
        child_bytecode_evals.push(verif.bytecode_evaluation);
        child_pub_inputs.push(child_pub_input);
        child_raw_proofs.push(raw_proof);
    }

    // Bytecode sumcheck reduction
    let (bytecode_claim_output, bytecode_point, final_sumcheck_transcript) = if n_recursions > 0 {
        let n_all_tweaks_fe =
            xmss::TWEAK_LEN + xmss::V * xmss::CHAIN_LENGTH * xmss::TWEAK_LEN + xmss::LOG_LIFETIME * xmss::TWEAK_LEN;
        let bytecode_claim_offset = 1 + DIGEST_LEN + 2 + MESSAGE_LEN_FE + N_MERKLE_CHUNKS_FOR_SLOT + n_all_tweaks_fe;
        let mut claims = vec![];
        for (i, _child) in children.iter().enumerate() {
            let first_claim = extract_bytecode_claim_from_public_input(
                &child_pub_inputs[i][bytecode_claim_offset..],
                bytecode_point_n_vars,
            );
            claims.push(first_claim);
            claims.push(child_bytecode_evals[i].clone());
        }

        let claims_hash = hash_bytecode_claims(&claims);

        let mut reduction_prover = build_prover_state();
        reduction_prover.add_base_scalars(&claims_hash);
        let alpha: EF = reduction_prover.sample();

        let n_claims = claims.len();
        let alpha_powers: Vec<EF> = alpha.powers().take(n_claims).collect();

        let weights_packed = claims
            .par_iter()
            .zip(&alpha_powers)
            .map(|(eval, &alpha_i)| eval_eq_packed_scaled(&eval.point.0, alpha_i))
            .reduce_with(|mut acc, eq_i| {
                acc.par_iter_mut().zip(&eq_i).for_each(|(w, e)| *w += *e);
                acc
            })
            .unwrap();

        let claimed_sum: EF = dot_product(claims.iter().map(|c| c.value), alpha_powers.iter().copied());

        let witness =
            MleGroupOwned::ExtensionPacked(vec![bytecode.instructions_multilinear_packed.clone(), weights_packed]);

        let (challenges, final_evals, _) = sumcheck_prove::<EF, _, _>(
            witness,
            &ProductComputation {},
            &vec![],
            None,
            &mut reduction_prover,
            claimed_sum,
            false,
        );

        let reduced_point = challenges;
        let reduced_value = final_evals[0];

        let mut ef_claim: Vec<EF> = reduced_point.0.clone();
        ef_claim.push(reduced_value);
        let claim_output = flatten_scalars_to_base::<F, EF>(&ef_claim);
        assert_eq!(claim_output.len(), bytecode_claim_size);

        let final_sumcheck_proof = {
            // Recover the transcript of the final sumcheck (for bytecode claim reduction)
            let mut vs = VerifierState::<EF, _>::new(reduction_prover.into_proof(), get_poseidon16().clone()).unwrap();
            vs.next_base_scalars_vec(claims_hash.len()).unwrap();
            let _: EF = vs.sample();
            sumcheck_verify(&mut vs, bytecode_point_n_vars, 2, claimed_sum, None).unwrap();
            vs.into_raw_proof().transcript
        };

        (claim_output, Some(reduced_point), final_sumcheck_proof)
    } else {
        let mut claim_output = vec![F::ZERO; bytecode_claim_size];
        claim_output[bytecode_point_n_vars * DIMENSION] = bytecode.instructions_multilinear[0];
        (claim_output, None, vec![])
    };

    // Build public input
    let slice_hash = hash_pubkeys(&global_pub_keys);
    let non_reserved_public_input = build_non_reserved_public_input(
        n_sigs,
        &slice_hash,
        message,
        slot,
        &bytecode_claim_output,
        &bytecode.hash,
    );
    let public_memory = build_public_memory(&non_reserved_public_input);

    // Build private input
    // Layout: [n_recursions, n_dup, ptr_pubkeys, ptr_source_0..n_recursions, ptr_bytecode_sumcheck,
    //          global_pubkeys, dup_pubkeys, source_blocks..., bytecode_sumcheck_proof]
    let header_size = n_recursions + 5;
    let pubkeys_start = public_memory.len() + header_size;

    // Build source blocks (also discovers duplicate pub_keys)
    let mut claimed: HashSet<XmssPublicKey> = HashSet::new();
    let mut dup_pub_keys: Vec<XmssPublicKey> = Vec::new();
    let mut source_blocks: Vec<Vec<F>> = vec![];

    // Build XMSS signatures (one Vec<F> per signature, consumed by hint_xmss)
    let xmss_signatures: Vec<Vec<F>> = raw_xmss.iter().map(|(_, sig)| encode_xmss_signature(sig)).collect();

    // Source 0: raw XMSS (indices only; signature data goes via hint_xmss)
    {
        let mut block = vec![F::from_usize(raw_count)];
        for (pk, _) in &raw_xmss {
            let pos = global_pub_keys.binary_search(pk).unwrap();
            block.push(F::from_usize(pos));
            claimed.insert(pk.clone());
        }
        source_blocks.push(block);
    }

    // Sources 1..n_recursions: recursive children
    for (i, child) in children.iter().enumerate() {
        let mut block = vec![F::from_usize(child.pub_keys.len())];
        for key in &child.pub_keys {
            if claimed.insert(key.clone()) {
                let pos = global_pub_keys.binary_search(key).unwrap();
                block.push(F::from_usize(pos));
            } else {
                block.push(F::from_usize(n_sigs + dup_pub_keys.len()));
                dup_pub_keys.push(key.clone());
            }
        }

        // bytecode_value_hint (DIM elements)
        block.extend_from_slice(child_bytecode_evals[i].value.as_basis_coefficients_slice());
        // inner_pub_mem
        let child_pub_mem = build_public_memory(&child_pub_inputs[i]);
        block.extend_from_slice(&child_pub_mem);
        // proof_transcript (without Merkle data, delivered via hint_merkle)
        block.extend_from_slice(&child_raw_proofs[i].transcript);

        source_blocks.push(block);
    }

    let n_dup = dup_pub_keys.len();
    let pubkey_fe_size = DIGEST_LEN + xmss::PUBLIC_PARAM_LEN_FE;
    let pubkeys_block_size = (n_sigs + n_dup) * pubkey_fe_size;

    // Compute absolute memory addresses for each source block
    let sources_start = pubkeys_start + pubkeys_block_size;
    let mut offset = sources_start;
    let mut source_ptrs: Vec<usize> = vec![];
    for block in &source_blocks {
        source_ptrs.push(offset);
        offset += block.len();
    }
    let bytecode_sumcheck_proof_ptr = offset;

    let mut private_input = vec![];
    private_input.push(F::from_usize(n_recursions));
    private_input.push(F::from_usize(n_dup));
    private_input.push(F::from_usize(pubkeys_start));
    for &ptr in &source_ptrs {
        private_input.push(F::from_usize(ptr));
    }
    private_input.push(F::from_usize(bytecode_sumcheck_proof_ptr));
    assert_eq!(private_input.len(), header_size);

    for pk in &global_pub_keys {
        private_input.extend_from_slice(&pk.merkle_root);
        private_input.extend_from_slice(&pk.public_param);
    }
    for pk in &dup_pub_keys {
        private_input.extend_from_slice(&pk.merkle_root);
        private_input.extend_from_slice(&pk.public_param);
    }
    for block in &source_blocks {
        private_input.extend_from_slice(block);
    }
    private_input.extend_from_slice(&final_sumcheck_transcript);

    // TODO precompute all the other poseidons
    let (xmss_poseidons_16_precomputed, xmss_poseidons_24_precomputed) = precompute_poseidons(&raw_xmss, message);

    // Build Merkle paths from all child proofs (one Vec<F> per hint_merkle call in whir.py)
    // Each opening produces two entries: leaf_data, then the flattened path.
    let merkle_paths: Vec<Vec<F>> = child_raw_proofs
        .iter()
        .flat_map(|p| p.merkle_openings.iter())
        .flat_map(|o| {
            let leaf = o.leaf_data.clone();
            let path: Vec<F> = o.path.iter().flat_map(|d| d.iter().copied()).collect();
            [leaf, path]
        })
        .collect();

    let witness = ExecutionWitness {
        private_input: &private_input,
        poseidons_16_precomputed: &xmss_poseidons_16_precomputed,
        poseidons_24_precomputed: &xmss_poseidons_24_precomputed,
        xmss_signatures: &xmss_signatures,
        merkle_paths: &merkle_paths,
    };
    let execution_proof = prove_execution(bytecode, &non_reserved_public_input, &witness, &whir_config, false);

    AggregatedXMSS {
        pub_keys: global_pub_keys,
        proof: execution_proof.proof,
        bytecode_point,
        metadata: Some(execution_proof.metadata),
    }
}

pub fn extract_bytecode_claim_from_public_input(public_input: &[F], bytecode_point_n_vars: usize) -> Evaluation<EF> {
    let claim_size = (bytecode_point_n_vars + 1) * DIMENSION;
    let packed = pack_scalars_to_extension(&public_input[..claim_size]);
    let point = MultilinearPoint(packed[..bytecode_point_n_vars].to_vec());
    let value = packed[bytecode_point_n_vars];
    Evaluation::new(point, value)
}

pub fn hash_bytecode_claims(claims: &[Evaluation<EF>]) -> [F; DIGEST_LEN] {
    let mut running_hash = [F::ZERO; DIGEST_LEN];
    for eval in claims {
        let mut ef_data: Vec<EF> = eval.point.0.clone();
        ef_data.push(eval.value);
        let mut data = flatten_scalars_to_base::<F, EF>(&ef_data);
        data.resize(data.len().next_multiple_of(DIGEST_LEN), F::ZERO);

        let claim_hash = poseidon_compress_slice(&data, false);
        running_hash = poseidon16_compress_pair(&running_hash, &claim_hash);
    }
    running_hash
}

#[instrument(skip_all)]
fn precompute_poseidons(
    raw_signers: &[(XmssPublicKey, XmssSignature)],
    message: &[F; MESSAGE_LEN_FE],
) -> (Poseidon16History, Poseidon24History) {
    let traces: Vec<_> = raw_signers
        .par_iter()
        .map(|(pub_key, sig)| xmss_verify_with_poseidon_trace(pub_key, message, sig).unwrap())
        .collect();
    let (p16s, p24s): (Vec<_>, Vec<_>) = traces.into_iter().unzip();
    (
        p16s.into_par_iter().flatten().collect(),
        p24s.into_par_iter().flatten().collect(),
    )
}
