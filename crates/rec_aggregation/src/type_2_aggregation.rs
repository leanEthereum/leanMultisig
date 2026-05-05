use backend::*;
use lean_prover::ProverError;
use lean_prover::SNARK_DOMAIN_SEP;
use lean_prover::prove_execution::prove_execution;
use lean_prover::verify_execution::verify_execution;
use lean_vm::*;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use utils::poseidon_compress_slice;
use utils::poseidon16_compress_pair;

use crate::compilation::{
    BYTECODE_CLAIM_OFFSET, MAX_RECURSIONS, PREAMBLE_MEMORY_LEN, TYPE2_FLAG, get_aggregation_bytecode,
};
use crate::type_1_aggregation::{
    AggregationProof, TypeOneInfo, TypeOneMultiSignature, VerifiedChildren, build_type1_input_data,
    bytecode_claim_output_from_point, extract_merkle_hint_blobs, flatten_bytecode_claim,
    verify_children_and_reduce_claims,
};

/// Type-2 multi-signature: A bundle of `n` type-1 multi-signatures with potentially distinct (message,
/// slot) per component, attested to by a single recursive SNARK.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TypeTwoMultiSignature {
    pub info: Vec<TypeOneInfo>,
    pub component_bytecode_points: Vec<MultilinearPoint<EF>>,
    pub proof: AggregationProof,
}

/// Reconstruct the type-1 public-input data buffer from `info` and the
/// component's saved `bytecode_point`.
pub(crate) fn type1_input_data_from_parts(info: &TypeOneInfo, bytecode_point: &MultilinearPoint<EF>) -> Vec<F> {
    let claim_output = bytecode_claim_output_from_point(bytecode_point);
    build_type1_input_data(&info.pubkeys, &info.message, info.slot, &claim_output)
}

/// The 8-FE digest the type-2 buffer commits to per component (= the type-1
/// public-input hash for that component).
fn type1_component_digest(info: &TypeOneInfo, bytecode_point: &MultilinearPoint<EF>) -> [F; DIGEST_LEN] {
    poseidon_compress_slice(&type1_input_data_from_parts(info, bytecode_point), true)
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

    let mut info_vec: Vec<TypeOneInfo> = Vec::with_capacity(n_components);
    let mut component_bytecode_points: Vec<MultilinearPoint<EF>> = Vec::with_capacity(n_components);
    let helper_pairs = type_1_multi_signatures.into_iter().map(|sig| {
        assert!(sig.info.pubkeys.is_sorted(), "component pubkeys must be sorted");
        let TypeOneMultiSignature { info, proof } = sig;
        let claim_output = proof.bytecode_claim_flat();
        let input_data = build_type1_input_data(&info.pubkeys, &info.message, info.slot, &claim_output);
        info_vec.push(info);
        component_bytecode_points.push(proof.bytecode_point.clone());
        (input_data, proof.execution_proof.proof)
    });

    let VerifiedChildren {
        pub_mem_digests: digests,
        child_input_data,
        child_bytecode_evals,
        child_raw_proofs,
        bytecode_claim_output,
        reduced_point,
        reduced_value,
        sumcheck_transcript,
        ..
    } = verify_children_and_reduce_claims(helper_pairs);

    let pub_input_data = build_type2_input_data_skeleton(&digests, &bytecode_claim_output);
    let public_input = poseidon_compress_slice(&pub_input_data, true).to_vec();

    let bytecode_value_hint_blobs: Vec<Vec<F>> = child_bytecode_evals
        .iter()
        .map(|eval| eval.value.as_basis_coefficients_slice().to_vec())
        .collect();

    // The bytecode materializes each component's full type-1 layout in one
    // shot and binds it to the committed digest by hash, so we just forward
    // the layout verbatim — its claim region is what gets used as the
    // forwarded claim in the soundness chain.
    let component_layout_blobs: Vec<Vec<F>> = child_input_data;

    let proof_transcript_blobs: Vec<Vec<F>> = child_raw_proofs.iter().map(|p| p.transcript.clone()).collect();
    let (merkle_leaf_blobs, merkle_path_blobs) = extract_merkle_hint_blobs(&child_raw_proofs);

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
    hints.insert("bytecode_sumcheck_proof".to_string(), vec![sumcheck_transcript]);

    let witness = ExecutionWitness {
        preamble_memory_len: PREAMBLE_MEMORY_LEN,
        hints,
    };
    let execution_proof = prove_execution(bytecode, &public_input, &witness, &whir_config, false)?;

    Ok(TypeTwoMultiSignature {
        info: info_vec,
        component_bytecode_points,
        proof: AggregationProof {
            execution_proof,
            bytecode_point: reduced_point,
            bytecode_value: reduced_value,
        },
    })
}

/// Verify a type-2 multi-signature: recompute each component's type-1 digest
/// from `info[i]` + `component_bytecode_points[i]`, hash the assembled outer
/// buffer, and verify the SNARK proof.
pub fn verify_type_2(sig: &TypeTwoMultiSignature) -> Result<(), ProofError> {
    if sig.info.is_empty() || sig.info.len() > MAX_RECURSIONS {
        return Err(ProofError::InvalidProof);
    }
    if sig.info.len() != sig.component_bytecode_points.len() {
        return Err(ProofError::InvalidProof);
    }

    let bytecode = get_aggregation_bytecode();

    let bytecode_claim_output = flatten_bytecode_claim(&sig.proof.bytecode_point, sig.proof.bytecode_value);

    let digests: Vec<[F; DIGEST_LEN]> = sig
        .info
        .iter()
        .zip(&sig.component_bytecode_points)
        .map(|(info, bp)| type1_component_digest(info, bp))
        .collect();

    let pub_input_data = build_type2_input_data_skeleton(&digests, &bytecode_claim_output);
    let public_input = poseidon_compress_slice(&pub_input_data, true).to_vec();

    verify_execution(bytecode, &public_input, sig.proof.execution_proof.proof.clone()).map(|_| ())
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
    assert_eq!(
        n_components,
        type_2_multi_signature.component_bytecode_points.len(),
        "type-2 info / component_bytecode_points length mismatch"
    );
    let whir_config = lean_prover::default_whir_config(log_inv_rate);

    let bytecode = get_aggregation_bytecode();

    let TypeTwoMultiSignature {
        mut info,
        component_bytecode_points,
        proof: outer_proof,
    } = type_2_multi_signature;

    // Recompute per-component digests + each component's type-1 layout (the
    // kept component's layout is what the split SNARK takes as its outer data,
    // and we also need each component's bytecode_claim to feed the kept-claim hint).
    let mut component_data: Vec<Vec<F>> = info
        .iter()
        .zip(&component_bytecode_points)
        .map(|(info, bp)| type1_input_data_from_parts(info, bp))
        .collect();

    let type2_bytecode_claim_output = outer_proof.bytecode_claim_flat();
    let outer_digests: Vec<[F; DIGEST_LEN]> = component_data
        .iter()
        .map(|d| poseidon_compress_slice(d, true))
        .collect();
    let type2_input_data = build_type2_input_data_skeleton(&outer_digests, &type2_bytecode_claim_output);

    let VerifiedChildren {
        mut child_input_data,
        mut child_bytecode_evals,
        mut child_raw_proofs,
        bytecode_claim_output,
        reduced_point,
        reduced_value,
        sumcheck_transcript,
        ..
    } = verify_children_and_reduce_claims(std::iter::once((type2_input_data, outer_proof.execution_proof.proof)));
    let bytecode_value_hint_blob: Vec<F> = child_bytecode_evals
        .pop()
        .unwrap()
        .value
        .as_basis_coefficients_slice()
        .to_vec();
    let raw_proof = child_raw_proofs.pop().unwrap();
    let inner_type2_layout = child_input_data.pop().unwrap();

    // Outer (split) public input: type-1 layout for the kept component, with the SPLIT's
    // reduced claim (not the original component's claim).
    let kept_info = info.swap_remove(index);
    let pub_input_data = build_type1_input_data(
        &kept_info.pubkeys,
        &kept_info.message,
        kept_info.slot,
        &bytecode_claim_output,
    );
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
    hints.insert("bytecode_sumcheck_proof".to_string(), vec![sumcheck_transcript]);

    let witness = ExecutionWitness {
        preamble_memory_len: PREAMBLE_MEMORY_LEN,
        hints,
    };
    let execution_proof = prove_execution(bytecode, &public_input, &witness, &whir_config, false)?;

    Ok(TypeOneMultiSignature {
        info: kept_info,
        proof: AggregationProof {
            execution_proof,
            bytecode_point: reduced_point,
            bytecode_value: reduced_value,
        },
    })
}
