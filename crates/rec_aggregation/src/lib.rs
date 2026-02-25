#![cfg_attr(not(test), allow(unused_crate_dependencies))]
use backend::*;
use lean_prover::prove_execution::prove_execution;
use lean_prover::verify_execution::ProofVerificationDetails;
use lean_prover::verify_execution::verify_execution;
use lean_vm::*;
use tracing::instrument;
use utils::{build_prover_state, poseidon_compress_slice, poseidon16_compress_pair};
use xmss::{
    LOG_LIFETIME, MESSAGE_LEN_FE, Poseidon16History, SIG_SIZE_FE, XmssPublicKey, XmssSignature, slot_to_field_elements,
    xmss_verify_with_poseidon_trace,
};

use serde::{Deserialize, Serialize};
use std::collections::HashSet;

use crate::compilation::get_aggregation_bytecode;

pub mod benchmark;
pub mod compilation;

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

pub fn hash_pubkeys(pub_keys: &[XmssPublicKey]) -> [F; DIGEST_LEN] {
    let iv = [F::ZERO; DIGEST_LEN];
    let flat: Vec<F> = iv
        .iter()
        .copied()
        .chain(pub_keys.iter().flat_map(|pk| pk.merkle_root.iter().copied()))
        .collect();
    poseidon_compress_slice(&flat)
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

fn build_non_reserved_public_input(
    n_sigs: usize,
    slice_hash: &[F; DIGEST_LEN],
    message: &[F; MESSAGE_LEN_FE],
    slot: u32,
    bytecode_claim_output: &[F],
) -> Vec<F> {
    let mut pi = vec![];
    pi.push(F::from_usize(n_sigs));
    pi.extend_from_slice(slice_hash);
    pi.extend_from_slice(message);
    let [slot_lo, slot_hi] = slot_to_field_elements(slot);
    pi.push(slot_lo);
    pi.push(slot_hi);
    pi.extend(compute_merkle_chunks_for_slot(slot));
    pi.extend_from_slice(bytecode_claim_output);
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
    pub proof: PrunedProof<F>,
    pub bytecode_point: Option<MultilinearPoint<EF>>,
    // benchmark / debug purpose
    #[serde(skip, default)]
    pub metadata: Option<ExecutionMetadata>,
}

impl AggregatedXMSS {
    pub fn raw_proof(&self) -> Option<RawProof<F>> {
        self.proof.clone().restore().map(|p| p.into_raw_proof())
    }

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
        assert_eq!(bytecode_claim_output.len(), bytecode_claim_size);

        let slice_hash = hash_pubkeys(&self.pub_keys);

        build_non_reserved_public_input(self.pub_keys.len(), &slice_hash, message, slot, &bytecode_claim_output)
    }
}

pub fn verify_aggregation(
    agg_sig: &AggregatedXMSS,
    message: &[F; MESSAGE_LEN_FE],
    slot: u32,
) -> Result<ProofVerificationDetails, ProofError> {
    if !agg_sig.pub_keys.is_sorted() {
        return Err(ProofError::InvalidProof);
    }
    let public_input = agg_sig.public_input(message, slot);
    let bytecode = get_aggregation_bytecode();
    verify_execution(
        bytecode,
        &public_input,
        agg_sig.raw_proof().ok_or(ProofError::InvalidProof)?,
    )
}

/// panics if one of the sub-proof (children) is invalid
#[instrument(skip_all)]
pub fn aggregate(
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
        let raw_proof = child
            .proof
            .clone()
            .restore()
            .expect("invalid child proof")
            .into_raw_proof();
        let verif = verify_execution(bytecode, &child_pub_input, raw_proof.clone()).unwrap();
        child_bytecode_evals.push(verif.bytecode_evaluation);
        child_pub_inputs.push(child_pub_input);
        child_raw_proofs.push(raw_proof);
    }

    // Bytecode sumcheck reduction
    let (bytecode_claim_output, bytecode_point, final_sumcheck_transcript) = if n_recursions > 0 {
        let bytecode_claim_offset = 1 + DIGEST_LEN + 2 + MESSAGE_LEN_FE + N_MERKLE_CHUNKS_FOR_SLOT;
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
            None,
            &ProductComputation {},
            &vec![],
            None,
            false,
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

        (
            claim_output,
            Some(reduced_point),
            reduction_prover.raw_proof().transcript,
        )
    } else {
        let mut claim_output = vec![F::ZERO; bytecode_claim_size];
        claim_output[bytecode_point_n_vars * DIMENSION] = bytecode.instructions_multilinear[0];
        (claim_output, None, vec![])
    };

    // Build public input
    let slice_hash = hash_pubkeys(&global_pub_keys);
    let non_reserved_public_input =
        build_non_reserved_public_input(n_sigs, &slice_hash, message, slot, &bytecode_claim_output);
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
    let pubkeys_block_size = n_sigs * DIGEST_LEN + n_dup * DIGEST_LEN;

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
    }
    for pk in &dup_pub_keys {
        private_input.extend_from_slice(&pk.merkle_root);
    }
    for block in &source_blocks {
        private_input.extend_from_slice(block);
    }
    private_input.extend_from_slice(&final_sumcheck_transcript);

    // TODO precompute all the other poseidons
    let xmss_poseidons_16_precomputed = precompute_poseidons(&raw_xmss, message);

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

        let claim_hash = poseidon_compress_slice(&data);
        running_hash = poseidon16_compress_pair(running_hash, claim_hash);
    }
    running_hash
}

#[instrument(skip_all)]
fn precompute_poseidons(
    raw_signers: &[(XmssPublicKey, XmssSignature)],
    message: &[F; MESSAGE_LEN_FE],
) -> Poseidon16History {
    let traces: Vec<_> = raw_signers
        .par_iter()
        .map(|(pub_key, sig)| xmss_verify_with_poseidon_trace(pub_key, message, sig).unwrap())
        .collect();
    traces.into_par_iter().flatten().collect()
}
