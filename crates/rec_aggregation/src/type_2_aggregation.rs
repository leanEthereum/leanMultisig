use backend::*;
use lean_prover::ProverError;
use lean_prover::SNARK_DOMAIN_SEP;
use lean_prover::prove_execution::ExecutionProof;
use lean_prover::prove_execution::prove_execution;
use lean_vm::*;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use utils::poseidon_compress_slice;
use utils::poseidon16_compress_pair;

use crate::compilation::{
    BYTECODE_CLAIM_OFFSET, MAX_RECURSIONS, PREAMBLE_MEMORY_LEN, TYPE2_FLAG, get_aggregation_bytecode,
};
use crate::type_1_aggregation::compute_bytecode_value_at;
use crate::type_1_aggregation::flatten_bytecode_claim;
use crate::type_1_aggregation::{
    InnerVerified, TypeOneInfo, TypeOneMultiSignature, extract_merkle_hint_blobs, reduce_bytecode_claims, verify_inner,
    verify_type_1,
};

/// Type-2 multi-signature: A bundle of `n` type-1 multi-signatures with potentially distinct (message,
/// slot) per component, attested to by a single recursive snark.
#[derive(Debug, Clone)]
pub struct TypeTwoMultiSignature {
    pub info: Vec<TypeOneInfo>,
    pub bytecode_claim: Evaluation<EF>, // value is trusted to be correct  (should be recomputed when receiving a proof from an untrusted source)
    pub proof: ExecutionProof,
}

impl Serialize for TypeTwoMultiSignature {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        (&self.info, &self.bytecode_claim.point, &self.proof).serialize(s)
    }
}

impl<'de> Deserialize<'de> for TypeTwoMultiSignature {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let (info, bytecode_claim_point, proof) =
            <(Vec<TypeOneInfo>, MultilinearPoint<EF>, ExecutionProof)>::deserialize(d)?;
        if bytecode_claim_point.len() != get_aggregation_bytecode().total_n_vars() {
            return Err(serde::de::Error::custom("invalid bytecode point"));
        }
        let bytecode_value = compute_bytecode_value_at(&bytecode_claim_point);
        Ok(TypeTwoMultiSignature {
            info,
            bytecode_claim: Evaluation::new(bytecode_claim_point, bytecode_value),
            proof,
        })
    }
}

impl TypeTwoMultiSignature {
    pub fn serialize_compressed(&self) -> Vec<u8> {
        let encoded = postcard::to_allocvec(self).expect("postcard serialization failed");
        lz4_flex::compress_prepend_size(&encoded)
    }

    pub fn deserialize_compressed(bytes: &[u8]) -> Option<Self> {
        let decompressed = lz4_flex::decompress_size_prepended(bytes).ok()?;
        postcard::from_bytes(&decompressed).ok()
    }

    pub(crate) fn bytecode_claim_flat(&self) -> Vec<F> {
        flatten_bytecode_claim(&self.bytecode_claim)
    }
}

/// The 8-FE digest the type-2 buffer commits to per component (= the type-1
/// public-input hash for that component).
fn type1_component_digest(info: &TypeOneInfo) -> [F; DIGEST_LEN] {
    poseidon_compress_slice(&info.build_input_data(), true)
}

/// Builds the type-2 outer public-input data buffer (live region only).
/// Layout: [prefix(8) | bytecode_claim_padded | bytecode_hash_domsep(8) | n × digest(8)].
fn build_type2_input_data_skeleton(digests: &[[F; DIGEST_LEN]], bytecode_claim_output: &[F]) -> Vec<F> {
    let n = digests.len();
    let claim_padded = bytecode_claim_output.len().next_multiple_of(DIGEST_LEN);
    let domsep_offset = BYTECODE_CLAIM_OFFSET + claim_padded;
    let digests_offset = domsep_offset + DIGEST_LEN;
    let mut data = vec![F::ZERO; digests_offset + n * DIGEST_LEN];

    data[0] = F::from_usize(TYPE2_FLAG);
    data[1] = F::from_usize(n);
    // data[2..8] stays zero (prefix-chunk pad).

    data[BYTECODE_CLAIM_OFFSET..][..bytecode_claim_output.len()].copy_from_slice(bytecode_claim_output);
    let bytecode_hash = &get_aggregation_bytecode().hash;
    let domsep = poseidon16_compress_pair(bytecode_hash, &SNARK_DOMAIN_SEP);
    data[domsep_offset..][..DIGEST_LEN].copy_from_slice(&domsep);

    for (i, d) in digests.iter().enumerate() {
        let off = digests_offset + i * DIGEST_LEN;
        data[off..off + DIGEST_LEN].copy_from_slice(d);
    }

    data
}

/// Real-SNARK merge: produce a single recursive proof attesting to the
/// validity of all `type_1_multi_signatures` against their respective
/// (message, slot, pubkeys) tuples.
pub fn merge_many_type_1(
    type_1_multi_signatures: Vec<TypeOneMultiSignature>,
    log_inv_rate: usize,
) -> Result<TypeTwoMultiSignature, ProverError> {
    let n_components = type_1_multi_signatures.len();
    assert!(n_components > 0, "merge_many_type_1 requires at least one input");
    assert!(
        n_components <= MAX_RECURSIONS,
        "merge_many_type_1: at most {MAX_RECURSIONS} components are supported"
    );
    let whir_config = lean_prover::default_whir_config(log_inv_rate);

    let bytecode = get_aggregation_bytecode();

    let verified_children: Vec<InnerVerified> = type_1_multi_signatures
        .iter()
        .map(|sig| verify_type_1(sig).expect("component proof failed to verify"))
        .collect();

    let reduced_claims = reduce_bytecode_claims(&verified_children);

    let digests: Vec<[F; DIGEST_LEN]> = verified_children.iter().map(|v| v.input_data_hash).collect();
    let pub_input_data = build_type2_input_data_skeleton(&digests, &reduced_claims.final_claim_flat());
    let public_input = poseidon_compress_slice(&pub_input_data, true).to_vec();

    let bytecode_value_hint_blobs: Vec<Vec<F>> = verified_children
        .iter()
        .map(|v| v.bytecode_evaluation.value.as_basis_coefficients_slice().to_vec())
        .collect();

    // The bytecode materializes each component's full type-1 layout in one
    // shot and binds it to the committed digest by hash, so we just forward
    // the layout verbatim — its claim region is what gets used as the
    // forwarded claim in the soundness chain.
    let component_layout_blobs: Vec<Vec<F>> = verified_children.iter().map(|v| v.input_data.clone()).collect();

    let proof_transcript_blobs: Vec<Vec<F>> = verified_children
        .iter()
        .map(|v| v.raw_proof.transcript.clone())
        .collect();
    let (merkle_leaf_blobs, merkle_path_blobs) =
        extract_merkle_hint_blobs(verified_children.iter().map(|v| &v.raw_proof));

    let mut hints: HashMap<String, Vec<Vec<F>>> = HashMap::new();
    hints.insert(
        "input_data_num_chunks".to_string(),
        vec![vec![F::from_usize(pub_input_data.len() / DIGEST_LEN)]],
    );
    hints.insert("input_data".to_string(), vec![pub_input_data]);
    hints.insert("bytecode_value_hint".to_string(), bytecode_value_hint_blobs);
    hints.insert("component_layout".to_string(), component_layout_blobs);
    hints.insert(
        "proof_transcript_size".to_string(),
        proof_transcript_blobs
            .iter()
            .map(|b| vec![F::from_usize(b.len())])
            .collect(),
    );
    hints.insert("proof_transcript".to_string(), proof_transcript_blobs);
    hints.insert("merkle_leaf".to_string(), merkle_leaf_blobs);
    hints.insert("merkle_path".to_string(), merkle_path_blobs);
    hints.insert(
        "bytecode_sumcheck_proof".to_string(),
        vec![reduced_claims.sumcheck_transcript],
    );

    let witness = ExecutionWitness {
        preamble_memory_len: PREAMBLE_MEMORY_LEN,
        hints,
    };
    let execution_proof = prove_execution(bytecode, &public_input, &witness, &whir_config, false)?;

    Ok(TypeTwoMultiSignature {
        info: type_1_multi_signatures.into_iter().map(|sig| sig.info).collect(),
        bytecode_claim: reduced_claims.final_claim,
        proof: execution_proof,
    })
}

/// Verify a type-2 multi-signature: recompute each component's type-1 digest
/// from `info[i]` + `component_bytecode_points[i]`, hash the assembled outer
/// buffer, and verify the SNARK proof.
pub fn verify_type_2(sig: &TypeTwoMultiSignature) -> Result<InnerVerified, ProofError> {
    if sig.info.is_empty() || sig.info.len() > MAX_RECURSIONS {
        return Err(ProofError::InvalidProof);
    }
    let digests: Vec<[F; DIGEST_LEN]> = sig.info.iter().map(type1_component_digest).collect();
    let input_data = build_type2_input_data_skeleton(&digests, &sig.bytecode_claim_flat());
    verify_inner(input_data, sig.proof.proof.clone())
}

/// Recover an independent type-1 multi-signature for the component at `index`
/// from a type-2 multi-signature.
pub fn split_type_2(
    type_2_multi_signature: TypeTwoMultiSignature,
    index: usize,
    log_inv_rate: usize,
) -> Result<TypeOneMultiSignature, ProverError> {
    let n_components = type_2_multi_signature.info.len();
    assert!(index < n_components, "split index {index} out of bounds");
    assert!(
        n_components <= MAX_RECURSIONS,
        "split_type_2: at most {MAX_RECURSIONS} components are supported"
    );
    let whir_config = lean_prover::default_whir_config(log_inv_rate);

    let bytecode = get_aggregation_bytecode();

    // Verify the outer type-2 proof up-front; the resulting `InnerVerified`
    // carries the type-2 input layout (used as the inner kept-claim hint) plus
    // the natural bytecode evaluation that feeds the claim reduction.
    let outer_verified = verify_type_2(&type_2_multi_signature).expect("type-2 outer proof failed to verify");

    let TypeTwoMultiSignature { mut info, .. } = type_2_multi_signature;

    // Recompute per-component type-1 layouts; the kept component's layout is
    // what the split SNARK takes as its outer data.
    let mut component_data: Vec<Vec<F>> = info.iter().map(|type1| type1.build_input_data()).collect();

    let reduced_claims = reduce_bytecode_claims(std::slice::from_ref(&outer_verified));
    let bytecode_value_hint_blob: Vec<F> = outer_verified
        .bytecode_evaluation
        .value
        .as_basis_coefficients_slice()
        .to_vec();
    let raw_proof = outer_verified.raw_proof;
    let inner_type2_layout = outer_verified.input_data;

    // Outer (split) public input: type-1 layout for the kept component, with the SPLIT's
    // reduced claim (not the original component's claim).
    let mut kept_info = info.swap_remove(index);
    kept_info.bytecode_claim = reduced_claims.final_claim.clone();
    let pub_input_data = kept_info.build_input_data();
    let public_input = poseidon_compress_slice(&pub_input_data, true).to_vec();

    // The split bytecode reconstructs the inner type-2 layout and the kept
    // component's type-1 layout from these two full-layout hints. Hash bindings
    // (digest_kept ↔ type2_digests[kept_idx], hash(inner_layout) ↔ inner SNARK)
    // pin the hint contents to the verifier's expected values.
    let kept_type1_buff: Vec<F> = component_data.swap_remove(index);

    let (merkle_leaf_blobs, merkle_path_blobs) = extract_merkle_hint_blobs(std::slice::from_ref(&raw_proof));
    let proof_transcript = raw_proof.transcript;
    let proof_transcript_size = vec![F::from_usize(proof_transcript.len())];

    let mut hints: HashMap<String, Vec<Vec<F>>> = HashMap::new();
    hints.insert(
        "input_data_num_chunks".to_string(),
        vec![vec![F::from_usize(pub_input_data.len() / DIGEST_LEN)]],
    );
    hints.insert("input_data".to_string(), vec![pub_input_data]);
    hints.insert("is_split".to_string(), vec![vec![F::ONE]]);
    hints.insert(
        "type2_meta".to_string(),
        vec![vec![F::from_usize(n_components), F::from_usize(index)]],
    );
    hints.insert("inner_type2_layout".to_string(), vec![inner_type2_layout]);
    hints.insert("kept_type1_buff".to_string(), vec![kept_type1_buff]);
    hints.insert("bytecode_value_hint".to_string(), vec![bytecode_value_hint_blob]);
    hints.insert("proof_transcript_size".to_string(), vec![proof_transcript_size]);
    hints.insert("proof_transcript".to_string(), vec![proof_transcript]);
    hints.insert("merkle_leaf".to_string(), merkle_leaf_blobs);
    hints.insert("merkle_path".to_string(), merkle_path_blobs);
    hints.insert(
        "bytecode_sumcheck_proof".to_string(),
        vec![reduced_claims.sumcheck_transcript],
    );

    let witness = ExecutionWitness {
        preamble_memory_len: PREAMBLE_MEMORY_LEN,
        hints,
    };
    let execution_proof = prove_execution(bytecode, &public_input, &witness, &whir_config, false)?;

    Ok(TypeOneMultiSignature {
        info: kept_info,
        proof: execution_proof,
    })
}
