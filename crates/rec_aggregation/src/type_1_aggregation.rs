use backend::*;
use lean_prover::ProverError;
use lean_prover::SNARK_DOMAIN_SEP;
use lean_prover::prove_execution::{ExecutionProof, prove_execution};
use lean_vm::*;
use leansig_wrapper::{
    BASE, HASH_LEN_FE, LOG_LIFETIME, MESSAGE_LENGTH, MSG_LEN_FE, PARAMETER_LEN, SIG_SIZE_FE, V, XmssPublicKey,
    XmssSignature, chain_tweak, merkle_tweak, pubkey_merkle_root, pubkey_public_parameter, xmmss_revealed_chain_tips,
    xmss_encode_message, xmss_merkle_path, xmss_randomness,
};
use tracing::instrument;
use utils::{poseidon_compress_slice, poseidon16_compress_pair};

use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};

use crate::InnerVerified;
use crate::bytecode_claims::evaluation_for_bytecode_point;
use crate::bytecode_claims::flatten_bytecode_claim;
use crate::bytecode_claims::reduce_bytecode_claims;
use crate::compilation::{
    BYTECODE_CLAIM_OFFSET, MAX_RECURSIONS, MAX_XMSS_AGGREGATED, MAX_XMSS_DUPLICATES, N_MERKLE_CHUNKS_FOR_SLOT,
    PREAMBLE_MEMORY_LEN, TYPE1_FLAG, get_aggregation_bytecode, type1_input_data_size_padded,
};
use crate::{lz4_postcard_decode, lz4_postcard_encode, verify_inner};

const CHAIN_LENGTH: usize = BASE;
const PUB_KEY_FLAT_SIZE: usize = HASH_LEN_FE + PARAMETER_LEN;

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
    pub without_pubkeys: TypeOneInfoWithoutPubkeys,
    pub pubkeys: Vec<XmssPublicKey>,
}

// Aggregation of many signatures, all sharing the same (message, slot)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TypeOneMultiSignature {
    pub info: TypeOneInfo,
    pub proof: ExecutionProof,
}

impl Serialize for TypeOneInfo {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        (&self.without_pubkeys, &self.pubkeys).serialize(s)
    }
}

impl<'de> Deserialize<'de> for TypeOneInfo {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let (without_pubkeys, pubkeys) = <(TypeOneInfoWithoutPubkeys, Vec<XmssPublicKey>)>::deserialize(d)?;
        if !pubkeys.is_sorted() {
            return Err(serde::de::Error::custom("unsorted pubkeys"));
        }
        Ok(Self {
            without_pubkeys,
            pubkeys,
        })
    }
}

impl TypeOneMultiSignature {
    pub fn compress(&self) -> Vec<u8> {
        lz4_postcard_encode(self)
    }

    pub fn decompress(bytes: &[u8]) -> Option<Self> {
        lz4_postcard_decode(bytes)
    }

    pub fn compress_without_pubkeys(&self) -> Vec<u8> {
        lz4_postcard_encode(&(&self.info.without_pubkeys, &self.proof))
    }

    pub fn decompress_without_pubkeys(bytes: &[u8], pubkeys: Vec<XmssPublicKey>) -> Option<Self> {
        let (without_pubkeys, proof) = lz4_postcard_decode::<(TypeOneInfoWithoutPubkeys, ExecutionProof)>(bytes)?;
        let info = without_pubkeys.with_pubkeys(pubkeys)?;
        Some(Self { info, proof })
    }

    pub(crate) fn bytecode_claim_flat(&self) -> Vec<F> {
        self.info.bytecode_claim_flat()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeOneInfoWithoutPubkeys {
    pub message: [u8; MESSAGE_LENGTH],
    pub slot: u32,
    pub bytecode_claim: Evaluation<EF>,
}

impl Serialize for TypeOneInfoWithoutPubkeys {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        (&self.message, &self.slot, &self.bytecode_claim.point).serialize(s)
    }
}

impl<'de> Deserialize<'de> for TypeOneInfoWithoutPubkeys {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let (message, slot, bytecode_claim_point) =
            <([u8; MESSAGE_LENGTH], u32, MultilinearPoint<EF>)>::deserialize(d)?;
        let bytecode_claim = evaluation_for_bytecode_point(bytecode_claim_point)
            .ok_or_else(|| serde::de::Error::custom("invalid bytecode point"))?;
        Ok(Self {
            message,
            slot,
            bytecode_claim,
        })
    }
}

impl TypeOneInfoWithoutPubkeys {
    pub(crate) fn with_pubkeys(self, mut pubkeys: Vec<XmssPublicKey>) -> Option<TypeOneInfo> {
        pubkeys.sort();
        pubkeys.dedup();
        Some(TypeOneInfo {
            without_pubkeys: self,
            pubkeys,
        })
    }
}

impl TypeOneInfo {
    pub(crate) fn bytecode_claim_flat(&self) -> Vec<F> {
        flatten_bytecode_claim(&self.without_pubkeys.bytecode_claim)
    }

    pub fn compress_without_pubkeys(&self) -> Vec<u8> {
        lz4_postcard_encode(&self.without_pubkeys)
    }

    pub fn decompress_without_pubkeys(bytes: &[u8], pubkeys: Vec<XmssPublicKey>) -> Option<Self> {
        lz4_postcard_decode::<TypeOneInfoWithoutPubkeys>(bytes)?.with_pubkeys(pubkeys)
    }

    pub(crate) fn build_input_data(&self) -> Vec<F> {
        let tweak_table = compute_tweak_table(self.without_pubkeys.slot);
        let tweaks_hash = poseidon_compress_slice(&tweak_table, TWEAKS_HASHING_USE_IV);
        build_type1_input_data(
            self.pubkeys.len(),
            &hash_pubkeys(&self.pubkeys),
            &xmss_encode_message(&self.without_pubkeys.message),
            self.without_pubkeys.slot,
            &tweaks_hash,
            &self.bytecode_claim_flat(),
            &get_aggregation_bytecode().hash,
        )
    }
}

fn pub_key_flat(pk: &XmssPublicKey) -> Vec<F> {
    let mut data = Vec::with_capacity(PUB_KEY_FLAT_SIZE);
    data.extend_from_slice(&pubkey_merkle_root(pk));
    data.extend_from_slice(&pubkey_public_parameter(pk));
    data
}

pub(crate) fn hash_pubkeys(pub_keys: &[XmssPublicKey]) -> [F; DIGEST_LEN] {
    let flat: Vec<F> = pub_keys.iter().flat_map(pub_key_flat).collect();
    poseidon_compress_slice(&flat, true)
}

/// Tweak slots are 4-FE [tw[0], tw[1], 0, 0]
fn compute_tweak_table(slot: u32) -> Vec<F> {
    let mut table = Vec::new();

    let push_padded = |table: &mut Vec<F>, tweak: [F; 2]| {
        table.extend(tweak);
        table.extend(std::iter::repeat_n(F::ZERO, 2));
    };

    // Encoding tweak: encode_epoch(slot) = ((slot << 8) | TWEAK_SEPARATOR_MSG) in base-p
    let acc = ((slot as u64) << 8) | 0x02u64;
    let encoding_tweak = [F::from_u64(acc % F::ORDER_U64), F::from_u64(acc / F::ORDER_U64)];
    push_padded(&mut table, encoding_tweak);

    // Chain tweaks
    for i in 0..V {
        for s in 0..CHAIN_LENGTH {
            push_padded(&mut table, chain_tweak(slot, i as u32, s as u32));
        }
    }

    // Leaf tweak: tree_tweak(0, slot) for hashing chain ends into a leaf node
    push_padded(&mut table, merkle_tweak(0, slot));

    // Merkle tweaks
    for level in 0..LOG_LIFETIME {
        let parent_level = level + 1;
        let parent_index = if parent_level < 32 {
            ((slot as u64) >> parent_level) as u32
        } else {
            0
        };
        push_padded(&mut table, merkle_tweak(parent_level, parent_index));
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
    message: &[F; MSG_LEN_FE],
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
    // Pad up to a multiple of DIGEST_LEN so slice_hash_with_iv consumes the whole buffer.
    data.resize(data.len().next_multiple_of(DIGEST_LEN), F::ZERO);
    data
}

fn encode_xmss_signature(sig: &XmssSignature) -> Vec<F> {
    let mut data = vec![];
    data.extend_from_slice(xmss_randomness(sig));
    data.extend(
        xmmss_revealed_chain_tips(sig)
            .iter()
            .flat_map(|digest| digest.iter().copied()),
    );
    data.extend(xmss_merkle_path(sig).iter().flat_map(|digest| digest.iter().copied()));
    assert_eq!(data.len(), SIG_SIZE_FE);
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
    message: [u8; MESSAGE_LENGTH],
    slot: u32,
    log_inv_rate: usize,
) -> Result<TypeOneMultiSignature, ProverError> {
    assert!(children.len() <= MAX_RECURSIONS);
    for child in children {
        assert_eq!(
            child.info.without_pubkeys.message, message,
            "all children of a type-1 aggregation must share the same message"
        );
        assert_eq!(
            child.info.without_pubkeys.slot, slot,
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
        &xmss_encode_message(message),
        slot,
        &tweaks_hash,
        &reduced_claims.final_claim_flat(),
        &bytecode.hash,
    );
    let public_input = poseidon_compress_slice(&pub_input_data, true).to_vec();

    let mut claimed: HashSet<XmssPublicKey> = HashSet::new();
    let mut dup_pub_keys: Vec<XmssPublicKey> = Vec::new();

    let xmss_signature_blobs: Vec<Vec<F>> = raw_xmss.iter().map(|(_, sig)| encode_xmss_signature(sig)).collect();

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
        pubkeys_blob.extend(pub_key_flat(pk));
    }
    for pk in &dup_pub_keys {
        pubkeys_blob.extend(pub_key_flat(pk));
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
    hints.insert("xmss_signature".to_string(), xmss_signature_blobs);
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
            without_pubkeys: TypeOneInfoWithoutPubkeys {
                message: *message,
                slot,
                bytecode_claim: reduced_claims.final_claim,
            },
            pubkeys: global_pub_keys,
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
