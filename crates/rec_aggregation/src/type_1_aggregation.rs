use backend::*;
use lean_prover::ProverError;
use lean_prover::SNARK_DOMAIN_SEP;
use lean_prover::prove_execution::{ExecutionProof, prove_execution};
use lean_prover::verify_execution::verify_execution;
use lean_vm::*;
use tracing::instrument;
use utils::{build_prover_state, get_poseidon16, poseidon_compress_slice, poseidon16_compress_pair};
use xmss::CHAIN_LENGTH;
use xmss::make_tweak;
use xmss::{
    LOG_LIFETIME, MESSAGE_LEN_FE, PUB_KEY_FLAT_SIZE, TWEAK_TYPE_CHAIN, TWEAK_TYPE_ENCODING, TWEAK_TYPE_MERKLE,
    TWEAK_TYPE_WOTS_PK, V, WOTS_SIG_SIZE_FE, XmssPublicKey, XmssSignature,
};

use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};

use crate::compilation::{
    BYTECODE_CLAIM_OFFSET, MAX_RECURSIONS, MAX_XMSS_AGGREGATED, MAX_XMSS_DUPLICATES, N_MERKLE_CHUNKS_FOR_SLOT,
    PREAMBLE_MEMORY_LEN, TYPE1_FLAG, bytecode_reduction_sumcheck_proof_size, get_aggregation_bytecode,
    type1_input_data_size_padded,
};

/// Number of tweaks in the table: 1 encoding + V*CHAIN_LENGTH chains + 1 wots_pk + LOG_LIFETIME merkle
pub(crate) const N_TWEAKS: usize = 1 + V * CHAIN_LENGTH + 1 + LOG_LIFETIME;
/// All tweaks are stored as a 4-FE slot [tw[0], tw[1], 0, 0].
pub(crate) const TWEAK_SLOT_SIZE: usize = 4;
pub(crate) const TWEAK_TABLE_SIZE_FE_PADDED: usize = (N_TWEAKS * TWEAK_SLOT_SIZE).next_multiple_of(DIGEST_LEN);

pub(crate) const TWEAKS_HASHING_USE_IV: bool = false; // fixed size → no IV needed

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub(crate) struct Digest(pub [F; DIGEST_LEN]);

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct TypeOneInfo {
    pub message: [F; MESSAGE_LEN_FE],
    pub slot: u32,
    pub pubkeys: Vec<XmssPublicKey>,
}

#[derive(Debug, Clone)]
pub struct AggregationProof {
    pub execution_proof: ExecutionProof,
    pub bytecode_point: MultilinearPoint<EF>,
    pub bytecode_value: EF,
}

impl Serialize for AggregationProof {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        (&self.execution_proof, &self.bytecode_point).serialize(s)
    }
}

impl<'de> Deserialize<'de> for AggregationProof {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let (execution_proof, bytecode_point) = <(ExecutionProof, MultilinearPoint<EF>)>::deserialize(d)?;
        Ok(Self {
            bytecode_value: compute_bytecode_value_at(&bytecode_point),
            execution_proof,
            bytecode_point,
        })
    }
}

impl AggregationProof {
    pub fn serialize(&self) -> Vec<u8> {
        let encoded = postcard::to_allocvec(self).expect("postcard serialization failed");
        lz4_flex::compress_prepend_size(&encoded)
    }

    pub fn deserialize(bytes: &[u8]) -> Option<Self> {
        let decompressed = lz4_flex::decompress_size_prepended(bytes).ok()?;
        postcard::from_bytes(&decompressed).ok()
    }

    pub(crate) fn bytecode_claim_flat(&self) -> Vec<F> {
        flatten_bytecode_claim(&self.bytecode_point, self.bytecode_value)
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TypeOneMultiSignature {
    pub info: TypeOneInfo,
    pub proof: AggregationProof,
}

pub(crate) fn hash_pubkeys(pub_keys: &[XmssPublicKey]) -> Digest {
    let flat: Vec<F> = pub_keys.iter().flat_map(|pk| pk.flaten().into_iter()).collect();
    Digest(poseidon_compress_slice(&flat, true))
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

/// Builds the type-1 public-input data buffer.
/// Layout: [prefix(8) | bytecode_claim_padded | bytecode_hash_domsep(8) | pubkeys_hash | message | merkle_chunks | tweaks_hash].
pub(crate) fn build_input_data(
    n_sigs: usize,
    slice_hash: &[F; DIGEST_LEN],
    message: &[F; MESSAGE_LEN_FE],
    slot: u32,
    tweaks_hash: &[F; DIGEST_LEN],
    bytecode_claim_output: &[F],
    bytecode_hash: &[F; DIGEST_LEN],
) -> Vec<F> {
    let log_size = get_aggregation_bytecode().log_size();
    let mut data = Vec::with_capacity(type1_input_data_size_padded(log_size));
    data.push(F::from_usize(TYPE1_FLAG));
    data.push(F::from_usize(n_sigs));
    data.resize(DIGEST_LEN, F::ZERO);
    data.extend_from_slice(bytecode_claim_output);
    let claim_padding = bytecode_claim_output.len().next_multiple_of(DIGEST_LEN) - bytecode_claim_output.len();
    data.extend(std::iter::repeat_n(F::ZERO, claim_padding));
    data.extend_from_slice(&poseidon16_compress_pair(bytecode_hash, &SNARK_DOMAIN_SEP));
    data.extend_from_slice(slice_hash);
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

#[allow(missing_debug_implementations)]
pub struct InnerVerified {
    pub input_data: Vec<F>,
    pub input_data_hash: [F; DIGEST_LEN],
    pub bytecode_evaluation: Evaluation<EF>,
    pub raw_proof: RawProof<F>,
}

pub(crate) fn verify_inner(input_data: Vec<F>, proof: Proof<F>) -> Result<InnerVerified, ProofError> {
    let input_data_hash = poseidon_compress_slice(&input_data, true);
    let bytecode = get_aggregation_bytecode();
    let (verif, raw_proof) = verify_execution(bytecode, &input_data_hash, proof)?;
    Ok(InnerVerified {
        input_data,
        input_data_hash,
        bytecode_evaluation: verif.bytecode_evaluation,
        raw_proof,
    })
}

// assumes `bytecode_value` in TypeOneMultiSignature::proof is correct (it should not be read / deserialized from an untrusted source)
pub fn verify_type_1(sig: &TypeOneMultiSignature) -> Result<InnerVerified, ProofError> {
    if !sig.info.pubkeys.is_sorted() {
        return Err(ProofError::InvalidProof);
    }
    let claim_output = sig.proof.bytecode_claim_flat();
    let input_data = build_type1_input_data(&sig.info.pubkeys, &sig.info.message, sig.info.slot, &claim_output);
    verify_inner(input_data, sig.proof.execution_proof.proof.clone())
}

pub(crate) struct ReducedClaims {
    pub bytecode_eval: Evaluation<EF>,
    pub sumcheck_transcript: Vec<F>,
}

impl ReducedClaims {
    pub fn bytecode_claim_flat(&self) -> Vec<F> {
        flatten_bytecode_claim(&self.bytecode_eval.point, self.bytecode_eval.value)
    }
}

pub(crate) fn reduce_verified_claims(verified: &[InnerVerified]) -> ReducedClaims {
    let bytecode = get_aggregation_bytecode();
    let bytecode_point_n_vars = bytecode.total_n_vars();
    let bytecode_claim_size = bytecode.bytecode_claim_size();

    if verified.is_empty() {
        let zero_point = MultilinearPoint(vec![EF::ZERO; bytecode_point_n_vars]);
        let zero_value = compute_bytecode_value_at(&zero_point);
        return ReducedClaims {
            bytecode_eval: Evaluation::new(zero_point, zero_value),
            sumcheck_transcript: vec![],
        };
    }

    let mut claims = Vec::with_capacity(2 * verified.len());
    for v in verified {
        claims.push(extract_bytecode_claim_from_input_data(
            &v.input_data[BYTECODE_CLAIM_OFFSET..],
            bytecode_point_n_vars,
        ));
        claims.push(v.bytecode_evaluation.clone());
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

    let (reduced_point, final_evals, _) = sumcheck_prove::<EF, _, _>(
        witness,
        &ProductComputation {},
        &vec![],
        None,
        &mut reduction_prover,
        claimed_sum,
        false,
    );

    let reduced_value = final_evals[0];
    let bytecode_claim_output = flatten_bytecode_claim(&reduced_point, reduced_value);
    assert_eq!(bytecode_claim_output.len(), bytecode_claim_size);

    let sumcheck_transcript = {
        let mut vs = VerifierState::<EF, _>::new(reduction_prover.into_proof(), get_poseidon16().clone()).unwrap();
        vs.next_base_scalars_vec(claims_hash.len()).unwrap();
        let _: EF = vs.sample();
        sumcheck_verify(&mut vs, bytecode_point_n_vars, 2, claimed_sum, None).unwrap();
        vs.into_raw_proof().transcript
    };
    assert_eq!(
        sumcheck_transcript.len(),
        bytecode_reduction_sumcheck_proof_size(bytecode_point_n_vars),
        "bytecode claim-reduction sumcheck transcript length disagrees with the formula",
    );

    ReducedClaims {
        bytecode_eval: Evaluation::new(reduced_point, reduced_value),
        sumcheck_transcript,
    }
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

    let reduced_claims = reduce_verified_claims(&verified_children);

    let slice_hash = hash_pubkeys(&global_pub_keys);
    let pub_input_data = build_input_data(
        n_sigs,
        &slice_hash.0,
        message,
        slot,
        &tweaks_hash,
        &reduced_claims.bytecode_claim_flat(),
        &bytecode.hash,
    );
    let public_input = poseidon_compress_slice(&pub_input_data, true).to_vec();

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
            F::from_usize(pubkeys_blob.len()),
            F::from_usize(raw_count),
        ]],
    );
    hints.insert("pubkeys".to_string(), vec![pubkeys_blob]);
    hints.insert("raw_indices".to_string(), vec![raw_indices]);
    let fast_path = n_recursions == 1 && raw_count == 0 && dup_pub_keys.is_empty();
    let sub_indices_for_hints = if fast_path { Vec::new() } else { sub_indices_blobs };
    hints.insert("sub_indices".to_string(), sub_indices_for_hints);
    // Standard type-1 (not a split). `split_type_2` is the only caller that sets this to 1.
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
        hints.insert("bytecode_sumcheck_proof".to_string(), vec![reduced_claims.sumcheck_transcript]);
    }

    let witness = ExecutionWitness {
        preamble_memory_len: PREAMBLE_MEMORY_LEN,
        hints,
    };
    let execution_proof = prove_execution(bytecode, &public_input, &witness, &whir_config, false)?;

    Ok(TypeOneMultiSignature {
        info: TypeOneInfo {
            message: *message,
            slot,
            pubkeys: global_pub_keys,
        },
        proof: AggregationProof {
            execution_proof,
            bytecode_point: reduced_claims.bytecode_eval.point,
            bytecode_value: reduced_claims.bytecode_eval.value,
        },
    })
}

pub(crate) fn flatten_bytecode_claim(point: &MultilinearPoint<EF>, value: EF) -> Vec<F> {
    let mut ef_claim: Vec<EF> = point.0.clone();
    ef_claim.push(value);
    flatten_scalars_to_base::<F, EF>(&ef_claim)
}

pub(crate) fn compute_bytecode_value_at(point: &MultilinearPoint<EF>) -> EF {
    let bytecode = get_aggregation_bytecode();
    if point.iter().all(|x| x.is_zero()) {
        // fast path for multi-signatures coming from 100% raw XMSS (no recursion):
        EF::from(bytecode.instructions_multilinear[0])
    } else {
        bytecode.instructions_multilinear.evaluate(point)
    }
}

pub(crate) fn bytecode_claim_output_from_point(point: &MultilinearPoint<EF>) -> Vec<F> {
    flatten_bytecode_claim(point, compute_bytecode_value_at(point))
}

/// Builds the type-1 public-input data buffer from already-encoded parts.
/// Used by every flow that needs a type-1 layout: standalone aggregation,
/// per-component reconstruction in type-2 verification, and the kept-component
/// reconstruction in `split_type_2`.
pub(crate) fn build_type1_input_data(
    pubkeys: &[XmssPublicKey],
    message: &[F; MESSAGE_LEN_FE],
    slot: u32,
    bytecode_claim_output: &[F],
) -> Vec<F> {
    let slice_hash = hash_pubkeys(pubkeys);
    let tweak_table = compute_tweak_table(slot);
    let tweaks_hash = poseidon_compress_slice(&tweak_table, TWEAKS_HASHING_USE_IV);
    build_input_data(
        pubkeys.len(),
        &slice_hash.0,
        message,
        slot,
        &tweaks_hash,
        bytecode_claim_output,
        &get_aggregation_bytecode().hash,
    )
}

/// Flatten WHIR Merkle openings from a batch of recursive sub-proofs into the
/// `(merkle_leaf, merkle_path)` hint-blob pair the bytecode consumes.
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

pub(crate) fn extract_bytecode_claim_from_input_data(
    public_input: &[F],
    bytecode_point_n_vars: usize,
) -> Evaluation<EF> {
    let claim_size = (bytecode_point_n_vars + 1) * DIMENSION;
    let packed = pack_scalars_to_extension(&public_input[..claim_size]);
    let point = MultilinearPoint(packed[..bytecode_point_n_vars].to_vec());
    let value = packed[bytecode_point_n_vars];
    Evaluation::new(point, value)
}

pub(crate) fn hash_bytecode_claims(claims: &[Evaluation<EF>]) -> [F; DIGEST_LEN] {
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
