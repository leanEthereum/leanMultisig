#![cfg_attr(not(test), allow(unused_crate_dependencies))]
use backend::*;
use lean_prover::ProverError;
use lean_prover::SNARK_DOMAIN_SEP;
use lean_prover::prove_execution::prove_execution;
use lean_prover::verify_execution::ProofVerificationDetails;
use lean_prover::verify_execution::verify_execution;
use lean_vm::*;
use tracing::instrument;
use utils::{build_prover_state, get_poseidon16, poseidon_compress_slice, poseidon16_compress_pair};
use xmss::{LOG_LIFETIME, MESSAGE_LEN_FE, PUB_KEY_FLAT_SIZE, V, W, WOTS_SIG_SIZE_FE, XmssPublicKey, XmssSignature};

use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};

use crate::compilation::bytecode_reduction_sumcheck_proof_size;
pub use crate::compilation::{get_aggregation_bytecode, init_aggregation_bytecode};

pub mod benchmark;
mod compilation;

const MERKLE_LEVELS_PER_CHUNK_FOR_SLOT: usize = 4;
const N_MERKLE_CHUNKS_FOR_SLOT: usize = LOG_LIFETIME / MERKLE_LEVELS_PER_CHUNK_FOR_SLOT;
const CHAIN_LENGTH: usize = 1 << W;

// Tweak types (must match xmss crate)
const TWEAK_TYPE_CHAIN: usize = 0;
const TWEAK_TYPE_WOTS_PK: usize = 1;
const TWEAK_TYPE_MERKLE: usize = 2;
const TWEAK_TYPE_ENCODING: usize = 3;

/// Number of tweaks in the table: 1 encoding + V*CHAIN_LENGTH chains + 1 wots_pk + LOG_LIFETIME merkle
const N_TWEAKS: usize = 1 + V * CHAIN_LENGTH + 1 + LOG_LIFETIME;
/// All,  tweaks are stored as a 4-FE slot [tw[0], tw[1], 0, 0].
const TWEAK_SLOT_SIZE: usize = 4;
const TWEAK_TABLE_SIZE_FE_PADDED: usize = (N_TWEAKS * TWEAK_SLOT_SIZE).next_multiple_of(DIGEST_LEN);

const TWEAKS_HASHING_USE_IV: bool = false; // fixed size → no IV needed

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Digest(pub [F; DIGEST_LEN]);

// preamble memory layout: see `build_preamble_memory` in utils.py:
// [000.. (ZERO_VEC_LEN)][10000000 (fiat-shamir domain sep)][10000 (one in extension field)][111... (NUM_REPEATED_ONES)][tweak table]
pub const ZERO_VEC_LEN: usize = 16;
pub const NUM_REPEATED_ONES: usize = 32;
pub const PREAMBLE_MEMORY_LEN: usize =
    ZERO_VEC_LEN + DIGEST_LEN + DIMENSION + NUM_REPEATED_ONES + TWEAK_TABLE_SIZE_FE_PADDED;

#[derive(Debug, Clone)]
pub struct AggregationTopology {
    pub raw_xmss: usize,
    pub children: Vec<AggregationTopology>,
    pub log_inv_rate: usize,
    pub overlap: usize, // Ignored for leaves.
}

pub fn biggest_leaf(topology: &AggregationTopology) -> Option<AggregationTopology> {
    fn visit(t: &AggregationTopology, best: &mut Option<(usize, usize)>) {
        if t.raw_xmss > 0 && best.is_none_or(|(n, _)| t.raw_xmss > n) {
            *best = Some((t.raw_xmss, t.log_inv_rate));
        }
        for c in &t.children {
            visit(c, best);
        }
    }
    let mut best = None;
    visit(topology, &mut best);
    best.map(|(raw_xmss, log_inv_rate)| AggregationTopology {
        raw_xmss,
        children: vec![],
        log_inv_rate,
        overlap: 0,
    })
}

pub(crate) fn count_signers(topology: &AggregationTopology) -> usize {
    let child_count: usize = topology.children.iter().map(count_signers).sum();
    let n_overlaps = topology.children.len().saturating_sub(1);
    topology.raw_xmss + child_count - topology.overlap * n_overlaps
}

pub fn hash_pubkeys(pub_keys: &[XmssPublicKey]) -> Digest {
    let flat: Vec<F> = pub_keys.iter().flat_map(|pk| pk.flaten().into_iter()).collect();
    Digest(poseidon_compress_slice(&flat, true))
}

fn make_tweak_values(tweak_type: usize, sub_position: usize, index: u32) -> [F; 2] {
    let index_lo = (index & 0xFFFF) as usize;
    let index_hi = (index >> 16) as usize;
    [
        F::from_usize((tweak_type << 26) + (index_hi << 10) + sub_position),
        F::from_usize(index_lo),
    ]
}

/// Tweak slots are 4-FE [tw[0], tw[1], 0, 0]
fn compute_tweak_table(slot: u32) -> Vec<F> {
    let mut table = Vec::new();

    let push_padded = |table: &mut Vec<F>, tweak_type: usize, sub_position: usize, index: u32| {
        table.extend(make_tweak_values(tweak_type, sub_position, index));
        table.extend(std::iter::repeat_n(F::ZERO, 2));
    };

    // Encoding tweak
    push_padded(&mut table, TWEAK_TYPE_ENCODING, 0, slot);

    // Chain tweaks
    for i in 0..V {
        for s in 0..CHAIN_LENGTH {
            push_padded(&mut table, TWEAK_TYPE_CHAIN, i * CHAIN_LENGTH + s, slot);
        }
    }

    // WOTS_PK tweak
    push_padded(&mut table, TWEAK_TYPE_WOTS_PK, 0, slot);

    // Merkle tweaks
    for level in 0..LOG_LIFETIME {
        let parent_index = ((slot as u64) >> (level + 1)) as u32;
        push_padded(&mut table, TWEAK_TYPE_MERKLE, level + 1, parent_index);
    }
    table.resize(TWEAK_TABLE_SIZE_FE_PADDED, F::ZERO);
    table
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

/// Builds the (padded) public-input data buffer that ends up being hashed.
fn build_input_data(
    n_sigs: usize,
    slice_hash: &[F; DIGEST_LEN],
    message: &[F; MESSAGE_LEN_FE],
    slot: u32,
    tweaks_hash: &[F; DIGEST_LEN],
    bytecode_claim_output: &[F],
    bytecode_hash: &[F; DIGEST_LEN],
) -> Vec<F> {
    let mut data = vec![];
    data.push(F::from_usize(n_sigs));
    data.extend_from_slice(slice_hash);
    data.extend_from_slice(message);
    data.extend(compute_merkle_chunks_for_slot(slot));
    data.extend_from_slice(tweaks_hash);
    data.extend_from_slice(bytecode_claim_output);
    // Pad the bytecode claim itself up to DIGEST_LEN
    let claim_padding = bytecode_claim_output.len().next_multiple_of(DIGEST_LEN) - bytecode_claim_output.len();
    data.extend(std::iter::repeat_n(F::ZERO, claim_padding));
    data.extend_from_slice(&poseidon16_compress_pair(bytecode_hash, &SNARK_DOMAIN_SEP));
    // Round the whole buffer up to DIGEST_LEN so `slice_hash_with_iv` can absorb it chunk by chunk.
    data.resize(data.len().next_multiple_of(DIGEST_LEN), F::ZERO);
    data
}

pub(crate) fn hash_input_data(data: &[F]) -> [F; DIGEST_LEN] {
    assert_eq!(data.len() % DIGEST_LEN, 0);
    poseidon_compress_slice(data, true)
}

fn encode_wots_signature(sig: &XmssSignature) -> Vec<F> {
    let mut data = vec![];
    data.extend(sig.wots_signature.randomness.to_vec());
    data.extend(sig.wots_signature.chain_tips.iter().flat_map(|digest| digest.to_vec()));
    assert_eq!(data.len(), WOTS_SIG_SIZE_FE);
    data
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct AggregatedXMSS {
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

    pub(crate) fn input_data(&self, pub_keys: &[XmssPublicKey], message: &[F; MESSAGE_LEN_FE], slot: u32) -> Vec<F> {
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

        let slice_hash = hash_pubkeys(pub_keys);
        let tweak_table = compute_tweak_table(slot);
        let tweaks_hash = poseidon_compress_slice(&tweak_table, TWEAKS_HASHING_USE_IV);

        build_input_data(
            pub_keys.len(),
            &slice_hash.0,
            message,
            slot,
            &tweaks_hash,
            &bytecode_claim_output,
            &bytecode.hash,
        )
    }

    /// The 1-digest public input that the verifier passes to `verify_execution`.
    pub fn public_input_hash(&self, pub_keys: &[XmssPublicKey], message: &[F; MESSAGE_LEN_FE], slot: u32) -> Vec<F> {
        hash_input_data(&self.input_data(pub_keys, message, slot)).to_vec()
    }
}

pub fn xmss_verify_aggregation(
    pub_keys: &[XmssPublicKey],
    agg_sig: &AggregatedXMSS,
    message: &[F; MESSAGE_LEN_FE],
    slot: u32,
) -> Result<ProofVerificationDetails, ProofError> {
    if !pub_keys.is_sorted() {
        return Err(ProofError::InvalidProof);
    }
    let public_input = agg_sig.public_input_hash(pub_keys, message, slot);
    let bytecode = get_aggregation_bytecode();
    verify_execution(bytecode, &public_input, agg_sig.proof.clone()).map(|(details, _)| details)
}

/// Errors if a signature is invalid
#[instrument(skip_all)]
pub fn xmss_aggregate(
    children: &[(&[XmssPublicKey], AggregatedXMSS)],
    mut raw_xmss: Vec<(XmssPublicKey, XmssSignature)>,
    message: &[F; MESSAGE_LEN_FE],
    slot: u32,
    log_inv_rate: usize,
) -> Result<(Vec<XmssPublicKey>, AggregatedXMSS), ProverError> {
    raw_xmss.sort_by(|(a, _), (b, _)| a.cmp(b));
    raw_xmss.dedup_by(|(a, _), (b, _)| a == b);

    let n_recursions = children.len();
    let raw_count = raw_xmss.len();
    let whir_config = lean_prover::default_whir_config(log_inv_rate);

    let bytecode = get_aggregation_bytecode();
    let bytecode_point_n_vars = bytecode.log_size() + log2_ceil_usize(N_INSTRUCTION_COLUMNS);
    let bytecode_claim_size = (bytecode_point_n_vars + 1) * DIMENSION;

    // Build global_pub_keys as sorted deduplicated union
    let mut global_pub_keys: Vec<XmssPublicKey> = raw_xmss.iter().map(|(pk, _)| pk.clone()).collect();
    for (child_pub_keys, _) in children.iter() {
        assert!(child_pub_keys.is_sorted(), "child pub_keys must be sorted");
        global_pub_keys.extend_from_slice(child_pub_keys);
    }
    global_pub_keys.sort();
    global_pub_keys.dedup();
    let n_sigs = global_pub_keys.len();

    // Compute tweak table and its hash
    let tweak_table = compute_tweak_table(slot);
    let tweaks_hash = poseidon_compress_slice(&tweak_table, TWEAKS_HASHING_USE_IV);

    // Verify child proofs
    let mut child_input_data = vec![];
    let mut child_input_hashes = vec![];
    let mut child_bytecode_evals = vec![];
    let mut child_raw_proofs = vec![];
    for (child_pub_keys, child) in children {
        let input_data = child.input_data(child_pub_keys, message, slot);
        let input_data_hash = hash_input_data(&input_data);
        let (verif, raw_proof) = verify_execution(bytecode, &input_data_hash, child.proof.clone()).unwrap();
        child_bytecode_evals.push(verif.bytecode_evaluation);
        child_input_data.push(input_data);
        child_input_hashes.push(input_data_hash);
        child_raw_proofs.push(raw_proof);
    }

    // Bytecode sumcheck reduction
    let (bytecode_claim_output, bytecode_point, final_sumcheck_transcript) = if n_recursions > 0 {
        let bytecode_claim_offset = 1 + DIGEST_LEN + MESSAGE_LEN_FE + N_MERKLE_CHUNKS_FOR_SLOT + DIGEST_LEN;
        let mut claims = vec![];
        for (i, _child) in children.iter().enumerate() {
            let first_claim = extract_bytecode_claim_from_input_data(
                &child_input_data[i][bytecode_claim_offset..],
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
        assert_eq!(
            final_sumcheck_proof.len(),
            bytecode_reduction_sumcheck_proof_size(bytecode_point_n_vars),
            "bytecode claim-reduction sumcheck transcript length disagrees with the formula",
        );

        (claim_output, Some(reduced_point), final_sumcheck_proof)
    } else {
        let mut claim_output = vec![F::ZERO; bytecode_claim_size];
        claim_output[bytecode_point_n_vars * DIMENSION] = bytecode.instructions_multilinear[0];
        (claim_output, None, vec![])
    };

    let slice_hash = hash_pubkeys(&global_pub_keys);
    let pub_input_data = build_input_data(
        n_sigs,
        &slice_hash.0,
        message,
        slot,
        &tweaks_hash,
        &bytecode_claim_output,
        &bytecode.hash,
    );
    let public_input = hash_input_data(&pub_input_data).to_vec();

    let mut claimed: HashSet<XmssPublicKey> = HashSet::new();
    let mut dup_pub_keys: Vec<XmssPublicKey> = Vec::new();

    // Raw XMSS data is split into two named hints — `wots` (randomness | chain_tips,
    // one entry per signature) and `xmss_merkle_node` (one entry per 4-FE merkle node,
    // flattened in the order `do_4_merkle_levels` consumes them at runtime).
    let wots_blobs: Vec<Vec<F>> = raw_xmss.iter().map(|(_, sig)| encode_wots_signature(sig)).collect();
    let xmss_merkle_node_blobs: Vec<Vec<F>> = raw_xmss
        .iter()
        .flat_map(|(_, sig)| sig.merkle_proof.iter().map(|d| d.to_vec()))
        .collect();

    // Raw XMSS indices.
    let raw_indices: Vec<F> = raw_xmss
        .iter()
        .map(|(pk, _)| {
            let pos = global_pub_keys.binary_search(pk).unwrap();
            claimed.insert(pk.clone());
            F::from_usize(pos)
        })
        .collect();

    let mut sub_indices_blobs = Vec::with_capacity(n_recursions);
    let mut bytecode_value_hint_blobs = Vec::with_capacity(n_recursions);
    let mut inner_bytecode_claim_blobs = Vec::with_capacity(n_recursions);
    let mut proof_transcript_blobs = Vec::with_capacity(n_recursions);

    let claim_offset_in_input = 1 + DIGEST_LEN + MESSAGE_LEN_FE + N_MERKLE_CHUNKS_FOR_SLOT + DIGEST_LEN;
    let claim_size_padded = bytecode_claim_size.next_multiple_of(DIGEST_LEN);

    // Sources 1..n_recursions: recursive children
    for (i, (child_pub_keys, _)) in children.iter().enumerate() {
        // sub_indices: [n_sub, idx_0, idx_1, ...] into global_pub_keys + dup_pub_keys
        let mut sub_indices = vec![F::from_usize(child_pub_keys.len())];
        for pubkey in *child_pub_keys {
            if claimed.insert(pubkey.clone()) {
                let pos = global_pub_keys.binary_search(pubkey).unwrap();
                sub_indices.push(F::from_usize(pos));
            } else {
                sub_indices.push(F::from_usize(n_sigs + dup_pub_keys.len()));
                dup_pub_keys.push(pubkey.clone());
            }
        }
        sub_indices_blobs.push(sub_indices);

        bytecode_value_hint_blobs.push(child_bytecode_evals[i].value.as_basis_coefficients_slice().to_vec());

        inner_bytecode_claim_blobs.push(child_input_data[i][claim_offset_in_input..][..claim_size_padded].to_vec());

        // Transcript minus Merkle data;
        proof_transcript_blobs.push(child_raw_proofs[i].transcript.clone());
    }

    let n_dup = dup_pub_keys.len();

    let mut pubkeys_blob: Vec<F> = Vec::with_capacity((n_sigs + n_dup) * PUB_KEY_FLAT_SIZE);
    for pk in &global_pub_keys {
        pubkeys_blob.extend_from_slice(&pk.flaten());
    }
    for pk in &dup_pub_keys {
        pubkeys_blob.extend_from_slice(&pk.flaten());
    }

    let (merkle_leaf_blobs, merkle_path_blobs): (Vec<Vec<F>>, Vec<Vec<F>>) = child_raw_proofs
        .iter()
        .flat_map(|p| p.merkle_openings.iter())
        .map(|o| {
            let leaf = o.leaf_data.clone();
            let path: Vec<F> = o.path.iter().flat_map(|d| d.iter().copied()).collect();
            (leaf, path)
        })
        .unzip();

    let aggregate_sizes: Vec<F> = sub_indices_blobs.iter().map(|b| F::from_usize(b.len())).collect();

    let mut hints: HashMap<String, Vec<Vec<F>>> = HashMap::new();
    hints.insert("input_data".to_string(), vec![pub_input_data]);
    // [n_recursions, n_dup, pubkeys_len, n_raw_xmss]
    hints.insert(
        "meta".to_string(),
        vec![vec![
            F::from_usize(n_recursions),
            F::from_usize(n_dup),
            F::from_usize(pubkeys_blob.len()),
            F::from_usize(raw_count),
        ]],
    );
    hints.insert("pubkeys".to_string(), vec![pubkeys_blob]);
    hints.insert("raw_indices".to_string(), vec![raw_indices]);
    let fast_path = n_recursions == 1 && raw_count == 0 && dup_pub_keys.is_empty();
    let sub_indices_for_hints = if fast_path { Vec::new() } else { sub_indices_blobs };
    hints.insert("sub_indices".to_string(), sub_indices_for_hints);
    hints.insert("bytecode_value_hint".to_string(), bytecode_value_hint_blobs);
    hints.insert("inner_bytecode_claim".to_string(), inner_bytecode_claim_blobs);
    hints.insert(
        "proof_transcript_size".to_string(),
        proof_transcript_blobs
            .iter()
            .map(|b| vec![F::from_usize(b.len())])
            .collect(),
    );
    hints.insert("proof_transcript".to_string(), proof_transcript_blobs);
    hints.insert("wots".to_string(), wots_blobs);
    hints.insert("xmss_merkle_node".to_string(), xmss_merkle_node_blobs);
    hints.insert("merkle_leaf".to_string(), merkle_leaf_blobs);
    hints.insert("merkle_path".to_string(), merkle_path_blobs);
    hints.insert("aggregate_sizes".to_string(), vec![aggregate_sizes]);
    hints.insert("tweak_table".to_string(), vec![tweak_table]);
    if n_recursions > 0 {
        hints.insert("bytecode_sumcheck_proof".to_string(), vec![final_sumcheck_transcript]);
    }

    let witness = ExecutionWitness {
        preamble_memory_len: PREAMBLE_MEMORY_LEN,
        hints,
    };
    let execution_proof = prove_execution(bytecode, &public_input, &witness, &whir_config, false)?;

    Ok((
        global_pub_keys,
        AggregatedXMSS {
            proof: execution_proof.proof,
            bytecode_point,
            metadata: Some(execution_proof.metadata),
        },
    ))
}

pub fn extract_bytecode_claim_from_input_data(public_input: &[F], bytecode_point_n_vars: usize) -> Evaluation<EF> {
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
