use backend::*;
use lean_prover::ProverError;
use lean_prover::SNARK_DOMAIN_SEP;
use lean_prover::prove_execution::{ExecutionProof, prove_execution};
use lean_vm::*;
use tracing::instrument;
use utils::{poseidon_compress_slice, poseidon16_compress_pair};
use xmss::CHAIN_LENGTH;
use xmss::make_tweak;
use xmss::{
    LOG_LIFETIME, MESSAGE_LEN_FE, PUB_KEY_FLAT_SIZE, TWEAK_TYPE_CHAIN, TWEAK_TYPE_ENCODING, TWEAK_TYPE_MERKLE,
    TWEAK_TYPE_WOTS_PK, V, WOTS_SIG_SIZE_FE, XmssPublicKey, XmssSignature,
};

use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};

use crate::InnerVerified;
use crate::bytecode_claims::compute_bytecode_value_at;
use crate::bytecode_claims::flatten_bytecode_claim;
use crate::bytecode_claims::reduce_bytecode_claims;
use crate::compilation::{
    BYTECODE_CLAIM_OFFSET, MAX_RECURSIONS, MAX_XMSS_AGGREGATED, MAX_XMSS_DUPLICATES, N_MERKLE_CHUNKS_FOR_SLOT,
    PREAMBLE_MEMORY_LEN, TYPE1_FLAG, get_aggregation_bytecode, type1_input_data_size_padded,
};
use crate::verify_inner;

/// Number of tweaks in the table: 1 encoding + V*CHAIN_LENGTH chains + 1 wots_pk + LOG_LIFETIME merkle
pub(crate) const N_TWEAKS: usize = 1 + V * CHAIN_LENGTH + 1 + LOG_LIFETIME;
/// All tweaks are stored as a 4-FE slot [tw[0], tw[1], 0, 0].
pub(crate) const TWEAK_SLOT_SIZE: usize = 4;
pub(crate) const TWEAK_TABLE_SIZE_FE_PADDED: usize = (N_TWEAKS * TWEAK_SLOT_SIZE).next_multiple_of(DIGEST_LEN);

pub(crate) const TWEAKS_HASHING_USE_IV: bool = false; // fixed size → no IV needed

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub(crate) struct Digest(pub [F; DIGEST_LEN]);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeOneInfo {
    pub message: [F; MESSAGE_LEN_FE],
    pub slot: u32,
    pub pubkeys: Vec<XmssPublicKey>,
    pub bytecode_claim: Evaluation<EF>, // value is trusted to be correct (should be recomputed when receiving a proof from an untrusted source)
}

// Aggregation of many signatures, all sharing the same (message, slot)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TypeOneMultiSignature {
    pub info: TypeOneInfo,
    pub proof: ExecutionProof,
}

impl Serialize for TypeOneInfo {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        (&self.message, &self.slot, &self.pubkeys, &self.bytecode_claim.point).serialize(s)
    }
}

impl<'de> Deserialize<'de> for TypeOneInfo {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let (message, slot, pubkeys, bytecode_claim_point) =
            <([F; MESSAGE_LEN_FE], u32, Vec<XmssPublicKey>, MultilinearPoint<EF>)>::deserialize(d)?;
        if bytecode_claim_point.len() != get_aggregation_bytecode().cumulated_n_vars() {
            return Err(serde::de::Error::custom("invalid bytecode point"));
        }
        if !pubkeys.is_sorted() {
            return Err(serde::de::Error::custom("unsorted pubkeys"));
        }
        let bytecode_value = compute_bytecode_value_at(&bytecode_claim_point);
        Ok(Self {
            message,
            slot,
            pubkeys,
            bytecode_claim: Evaluation::new(bytecode_claim_point, bytecode_value),
        })
    }
}

impl TypeOneMultiSignature {
    pub fn compress(&self) -> Vec<u8> {
        let encoded = postcard::to_allocvec(self).expect("postcard serialization failed");
        lz4_flex::compress_prepend_size(&encoded)
    }

    pub fn decompress(bytes: &[u8]) -> Option<Self> {
        let decompressed = lz4_flex::decompress_size_prepended(bytes).ok()?;
        postcard::from_bytes(&decompressed).ok()
    }

    pub(crate) fn bytecode_claim_flat(&self) -> Vec<F> {
        self.info.bytecode_claim_flat()
    }
}

impl TypeOneInfo {
    pub(crate) fn bytecode_claim_flat(&self) -> Vec<F> {
        flatten_bytecode_claim(&self.bytecode_claim)
    }

    pub(crate) fn build_input_data(&self) -> Vec<F> {
        let tweak_table = compute_tweak_table(self.slot);
        let tweaks_hash = poseidon_compress_slice(&tweak_table, TWEAKS_HASHING_USE_IV);
        build_type1_input_data(
            self.pubkeys.len(),
            &hash_pubkeys(&self.pubkeys),
            &self.message,
            self.slot,
            &tweaks_hash,
            &self.bytecode_claim_flat(),
            &get_aggregation_bytecode().hash,
        )
    }
}

pub(crate) fn hash_pubkeys(pub_keys: &[XmssPublicKey]) -> [F; DIGEST_LEN] {
    let flat: Vec<F> = pub_keys.iter().flat_map(|pk| pk.flaten().into_iter()).collect();
    poseidon_compress_slice(&flat, true)
}

/// Tweak slots are 4-FE [tw[0], tw[1], 0, 0]
fn compute_tweak_table(slot: u32) -> Vec<F> {
    let mut table = Vec::new();

    let push_padded = |table: &mut Vec<F>, tweak_type: usize, sub_position: usize, index: u32| {
        table.extend(make_tweak(tweak_type, sub_position, index));
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
    (0..N_MERKLE_CHUNKS_FOR_SLOT)
        .map(|chunk_idx| {
            let nibble = (slot >> (chunk_idx * 4)) & 0xF;
            F::from_u32((!nibble) & 0xF)
        })
        .collect()
}

/// Layout: [prefix(8) | bytecode_claim_padded | bytecode_hash_domsep(8) | pubkeys_hash | message | merkle_chunks | tweaks_hash].
pub(crate) fn build_type1_input_data(
    n_sigs: usize,
    pubkeys_hash: &[F; DIGEST_LEN],
    message: &[F; MESSAGE_LEN_FE],
    slot: u32,
    tweaks_hash: &[F; DIGEST_LEN],
    bytecode_claim_flat: &[F],
    bytecode_hash: &[F; DIGEST_LEN],
) -> Vec<F> {
    let log_size = get_aggregation_bytecode().log_size();
    let mut data = Vec::with_capacity(type1_input_data_size_padded(log_size));
    data.push(F::from_usize(TYPE1_FLAG));
    data.push(F::from_usize(n_sigs));
    data.resize(DIGEST_LEN, F::ZERO);
    data.extend_from_slice(bytecode_claim_flat);
    let claim_padding = bytecode_claim_flat.len().next_multiple_of(DIGEST_LEN) - bytecode_claim_flat.len();
    data.extend(std::iter::repeat_n(F::ZERO, claim_padding));
    data.extend_from_slice(&poseidon16_compress_pair(bytecode_hash, &SNARK_DOMAIN_SEP));
    data.extend_from_slice(pubkeys_hash);
    data.extend_from_slice(message);
    data.extend(compute_merkle_chunks_for_slot(slot));
    data.extend_from_slice(tweaks_hash);
    data
}

fn encode_wots_signature(sig: &XmssSignature) -> Vec<F> {
    let mut data = vec![];
    data.extend(sig.wots_signature.randomness.to_vec());
    data.extend(sig.wots_signature.chain_tips.iter().flat_map(|digest| digest.to_vec()));
    assert_eq!(data.len(), WOTS_SIG_SIZE_FE);
    data
}

// assumes `bytecode_value` in TypeOneMultiSignature::proof is correct (it should not be read / deserialized from an untrusted source)
pub fn verify_type_1(sig: &TypeOneMultiSignature) -> Result<InnerVerified, ProofError> {
    if !sig.info.pubkeys.is_sorted() {
        return Err(ProofError::InvalidProof);
    }
    verify_inner(sig.info.build_input_data(), sig.proof.proof.clone())
}

/// Aggregate raw XMSS signatures and previously aggregated multi-signatures.
/// Type 1 = single message, single slot.
#[instrument(skip_all)]
pub fn aggregate_type_1(
    children: &[TypeOneMultiSignature],
    mut raw_xmss: Vec<(XmssPublicKey, XmssSignature)>,
    message: [F; MESSAGE_LEN_FE],
    slot: u32,
    log_inv_rate: usize,
) -> Result<TypeOneMultiSignature, ProverError> {
    assert!(children.len() <= MAX_RECURSIONS);
    for child in children {
        assert_eq!(
            child.info.message, message,
            "all children of a type-1 aggregation must share the same message"
        );
        assert_eq!(
            child.info.slot, slot,
            "all children of a type-1 aggregation must share the same slot"
        );
    }
    let message = &message;
    let verified_children: Vec<InnerVerified> = children
        .iter()
        .map(|c| verify_type_1(c).expect("child proof failed to verify"))
        .collect();
    let children: Vec<&[XmssPublicKey]> = children.iter().map(|c| c.info.pubkeys.as_slice()).collect();
    let children = children.as_slice();

    raw_xmss.sort_by(|(a, _), (b, _)| a.cmp(b));
    raw_xmss.dedup_by(|(a, _), (b, _)| a == b);

    let n_recursions = children.len();
    let raw_count = raw_xmss.len();
    let whir_config = lean_prover::default_whir_config(log_inv_rate);

    let bytecode = get_aggregation_bytecode();
    let bytecode_claim_size = bytecode.bytecode_claim_size();

    // Build global_pub_keys as sorted deduplicated union
    let mut global_pub_keys: Vec<XmssPublicKey> = raw_xmss.iter().map(|(pk, _)| pk.clone()).collect();
    for child_pub_keys in children.iter() {
        assert!(child_pub_keys.is_sorted(), "child pub_keys must be sorted");
        global_pub_keys.extend_from_slice(child_pub_keys);
    }
    global_pub_keys.sort();
    global_pub_keys.dedup();
    let n_sigs = global_pub_keys.len();
    assert!(n_sigs <= MAX_XMSS_AGGREGATED);

    let tweak_table = compute_tweak_table(slot);
    let tweaks_hash = poseidon_compress_slice(&tweak_table, TWEAKS_HASHING_USE_IV);

    let reduced_claims = reduce_bytecode_claims(&verified_children);

    let pub_input_data = build_type1_input_data(
        n_sigs,
        &hash_pubkeys(&global_pub_keys),
        message,
        slot,
        &tweaks_hash,
        &reduced_claims.final_claim_flat(),
        &bytecode.hash,
    );
    let public_input = poseidon_compress_slice(&pub_input_data, true).to_vec();

    let mut claimed: HashSet<XmssPublicKey> = HashSet::new();
    let mut dup_pub_keys: Vec<XmssPublicKey> = Vec::new();

    let wots_blobs: Vec<Vec<F>> = raw_xmss.iter().map(|(_, sig)| encode_wots_signature(sig)).collect();
    let xmss_merkle_node_blobs: Vec<Vec<F>> = raw_xmss
        .iter()
        .flat_map(|(_, sig)| sig.merkle_proof.iter().map(|d| d.to_vec()))
        .collect();

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

    let claim_size_padded = bytecode_claim_size.next_multiple_of(DIGEST_LEN);

    for (i, child_pub_keys) in children.iter().enumerate() {
        // sub_indices: [idx_0, idx_1, ...] into global_pub_keys + dup_pub_keys.
        // The length n_sub is communicated via the matching `aggregate_sizes` entry.
        let mut sub_indices = Vec::with_capacity(child_pub_keys.len());
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

        let v = &verified_children[i];
        bytecode_value_hint_blobs.push(v.bytecode_evaluation.value.as_basis_coefficients_slice().to_vec());
        inner_bytecode_claim_blobs.push(v.input_data[BYTECODE_CLAIM_OFFSET..][..claim_size_padded].to_vec());
        proof_transcript_blobs.push(v.raw_proof.transcript.clone());
    }

    let n_dup = dup_pub_keys.len();
    assert!(n_dup <= MAX_XMSS_DUPLICATES);

    let mut pubkeys_blob: Vec<F> = Vec::with_capacity((n_sigs + n_dup) * PUB_KEY_FLAT_SIZE);
    for pk in &global_pub_keys {
        pubkeys_blob.extend_from_slice(&pk.flaten());
    }
    for pk in &dup_pub_keys {
        pubkeys_blob.extend_from_slice(&pk.flaten());
    }

    let (merkle_leaf_blobs, merkle_path_blobs) =
        extract_merkle_hint_blobs(verified_children.iter().map(|v| &v.raw_proof));

    let aggregate_sizes: Vec<F> = sub_indices_blobs.iter().map(|b| F::from_usize(b.len())).collect();

    let mut hints: HashMap<String, Vec<Vec<F>>> = HashMap::new();
    hints.insert(
        "input_data_num_chunks".to_string(),
        vec![vec![F::from_usize(pub_input_data.len() / DIGEST_LEN)]],
    );
    hints.insert("input_data".to_string(), vec![pub_input_data]);
    // [n_recursions, n_dup, pubkeys_len, n_raw_xmss]
    hints.insert(
        "meta".to_string(),
        vec![vec![
            F::from_usize(n_recursions),
            F::from_usize(n_dup),
            F::from_usize(raw_count),
        ]],
    );
    hints.insert("pubkeys".to_string(), vec![pubkeys_blob]);
    hints.insert("raw_indices".to_string(), vec![raw_indices]);
    let fast_path = n_recursions == 1 && raw_count == 0 && dup_pub_keys.is_empty();
    let sub_indices_for_hints = if fast_path { Vec::new() } else { sub_indices_blobs };
    hints.insert("sub_indices".to_string(), sub_indices_for_hints);
    // Standard type-1 (not a split).
    hints.insert("is_split".to_string(), vec![vec![F::ZERO]]);
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
        hints.insert(
            "bytecode_sumcheck_proof".to_string(),
            vec![reduced_claims.sumcheck_transcript],
        );
    }

    let witness = ExecutionWitness {
        preamble_memory_len: PREAMBLE_MEMORY_LEN,
        hints,
    };
    let proof = prove_execution(bytecode, &public_input, &witness, &whir_config, false)?;

    Ok(TypeOneMultiSignature {
        info: TypeOneInfo {
            message: *message,
            slot,
            pubkeys: global_pub_keys,
            bytecode_claim: reduced_claims.final_claim,
        },
        proof,
    })
}

/// return `([merkle_leafs], [merkle_paths])`
pub(crate) fn extract_merkle_hint_blobs<'a>(
    raw_proofs: impl IntoIterator<Item = &'a RawProof<F>>,
) -> (Vec<Vec<F>>, Vec<Vec<F>>) {
    raw_proofs
        .into_iter()
        .flat_map(|p| p.merkle_openings.iter())
        .map(|o| {
            let leaf = o.leaf_data.clone();
            let path: Vec<F> = o.path.iter().flat_map(|d| d.iter().copied()).collect();
            (leaf, path)
        })
        .unzip()
}
