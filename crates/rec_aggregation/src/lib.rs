#![cfg_attr(not(test), allow(unused_crate_dependencies))]
use backend::*;
use lean_prover::prove_execution::prove_execution;
use lean_prover::verify_execution::ProofVerificationDetails;
use lean_prover::verify_execution::verify_execution;
use lean_vm::*;
use tracing::instrument;
use utils::{build_prover_state, poseidon_compress_slice, poseidon16_compress_pair};
use xmss::{
    LOG_LIFETIME, MESSAGE_LEN_FE, Poseidon16History, RANDOMNESS_LEN_FE, SIG_SIZE_FE, XmssPublicKey, XmssSignature,
    slot_to_field_elements, xmss_verify_with_poseidon_trace,
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
    let total = DIGEST_LEN + pub_keys.len() * DIGEST_LEN;
    let mut flat = vec![F::ZERO; total];
    // First DIGEST_LEN elements are already zero. Write pub keys directly at offsets.
    let mut off = DIGEST_LEN;
    for pk in pub_keys {
        flat[off..off + DIGEST_LEN].copy_from_slice(&pk.merkle_root);
        off += DIGEST_LEN;
    }
    poseidon_compress_slice(&flat)
}

fn compute_merkle_chunks_for_slot(slot: u32) -> [F; N_MERKLE_CHUNKS_FOR_SLOT] {
    std::array::from_fn(|chunk_idx| {
        let mut nibble_val: usize = 0;
        for bit in 0..4 {
            let level = chunk_idx * 4 + bit;
            let is_left = (((slot as u64) >> level) & 1) == 0;
            if is_left {
                nibble_val |= 1 << bit;
            }
        }
        F::from_usize(nibble_val)
    })
}

fn build_non_reserved_public_input(
    n_sigs: usize,
    slice_hash: &[F; DIGEST_LEN],
    message: &[F; MESSAGE_LEN_FE],
    slot: u32,
    bytecode_claim_output: &[F],
) -> Vec<F> {
    let total = 1 + DIGEST_LEN + MESSAGE_LEN_FE + 2 + N_MERKLE_CHUNKS_FOR_SLOT + bytecode_claim_output.len();
    let mut pi = Vec::with_capacity(total);
    // SAFETY: capacity is `total`, all elements written below
    unsafe { pi.set_len(total) };
    let mut off = 0;
    pi[off] = F::from_usize(n_sigs);
    off += 1;
    pi[off..off + DIGEST_LEN].copy_from_slice(slice_hash);
    off += DIGEST_LEN;
    pi[off..off + MESSAGE_LEN_FE].copy_from_slice(message);
    off += MESSAGE_LEN_FE;
    let [slot_lo, slot_hi] = slot_to_field_elements(slot);
    pi[off] = slot_lo;
    pi[off + 1] = slot_hi;
    off += 2;
    let chunks = compute_merkle_chunks_for_slot(slot);
    pi[off..off + N_MERKLE_CHUNKS_FOR_SLOT].copy_from_slice(&chunks);
    off += N_MERKLE_CHUNKS_FOR_SLOT;
    pi[off..off + bytecode_claim_output.len()].copy_from_slice(bytecode_claim_output);
    debug_assert_eq!(off + bytecode_claim_output.len(), total);
    pi
}

fn encode_xmss_signature(sig: &XmssSignature) -> Vec<F> {
    let mut data = Vec::with_capacity(SIG_SIZE_FE);
    // SAFETY: capacity is SIG_SIZE_FE, all bytes written below via copy_from_slice
    unsafe { data.set_len(SIG_SIZE_FE) };
    let mut off = 0;
    data[off..off + RANDOMNESS_LEN_FE].copy_from_slice(&sig.wots_signature.randomness);
    off += RANDOMNESS_LEN_FE;
    for digest in &sig.wots_signature.chain_tips {
        data[off..off + DIGEST_LEN].copy_from_slice(digest);
        off += DIGEST_LEN;
    }
    for neighbor in &sig.merkle_proof {
        data[off..off + DIGEST_LEN].copy_from_slice(neighbor);
        off += DIGEST_LEN;
    }
    debug_assert_eq!(off, SIG_SIZE_FE);
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
    verify_execution(
        bytecode,
        &public_input,
        agg_sig.raw_proof().ok_or(ProofError::InvalidProof)?,
    )
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

    let source_blocks_total: usize = source_blocks.iter().map(|b| b.len()).sum();
    let private_total = header_size + pubkeys_block_size + source_blocks_total + final_sumcheck_transcript.len();
    let mut private_input = Vec::with_capacity(private_total);
    // SAFETY: capacity is private_total, all elements written below via indexed assignment + copy_from_slice
    unsafe { private_input.set_len(private_total) };
    let mut off = 0;

    // Header
    private_input[off] = F::from_usize(n_recursions);
    private_input[off + 1] = F::from_usize(n_dup);
    private_input[off + 2] = F::from_usize(pubkeys_start);
    off += 3;
    for &ptr in &source_ptrs {
        private_input[off] = F::from_usize(ptr);
        off += 1;
    }
    private_input[off] = F::from_usize(bytecode_sumcheck_proof_ptr);
    off += 1;
    debug_assert_eq!(off, header_size);

    // Pub keys
    for pk in &global_pub_keys {
        private_input[off..off + DIGEST_LEN].copy_from_slice(&pk.merkle_root);
        off += DIGEST_LEN;
    }
    for pk in &dup_pub_keys {
        private_input[off..off + DIGEST_LEN].copy_from_slice(&pk.merkle_root);
        off += DIGEST_LEN;
    }

    // Source blocks
    for block in &source_blocks {
        let blen = block.len();
        private_input[off..off + blen].copy_from_slice(block);
        off += blen;
    }

    // Bytecode sumcheck transcript
    let tlen = final_sumcheck_transcript.len();
    private_input[off..off + tlen].copy_from_slice(&final_sumcheck_transcript);
    debug_assert_eq!(off + tlen, private_total);

    // TODO precompute all the other poseidons
    let xmss_poseidons_16_precomputed = precompute_poseidons(&raw_xmss, message);

    // Build Merkle paths from all child proofs (one Vec<F> per hint_merkle call in whir.py)
    // Each opening produces two entries: leaf_data, then the flattened path.
    let merkle_paths: Vec<Vec<F>> = child_raw_proofs
        .iter()
        .flat_map(|p| p.merkle_openings.iter())
        .flat_map(|o| {
            let path_len = o.path.len() * DIGEST_LEN;
            let mut path = Vec::with_capacity(path_len);
            // SAFETY: capacity is path_len, all elements written below
            unsafe { path.set_len(path_len) };
            let mut off = 0;
            for d in &o.path {
                path[off..off + DIGEST_LEN].copy_from_slice(d);
                off += DIGEST_LEN;
            }
            [o.leaf_data.clone(), path]
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
