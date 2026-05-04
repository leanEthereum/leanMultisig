use backend::*;
use lean_prover::ProverError;
use lean_prover::SNARK_DOMAIN_SEP;
use lean_prover::prove_execution::prove_execution;
use lean_prover::verify_execution::verify_execution;
use lean_vm::*;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use utils::{poseidon_compress_slice, poseidon16_compress_pair};
use xmss::{MESSAGE_LEN_FE, XmssPublicKey, XmssSignature};

use crate::compilation::{TYPE2_BYTECODE_CLAIM_OFFSET, TYPE2_HEADERS_OFFSET};
use crate::{
    AggregatedXMSS, Digest, N_MERKLE_CHUNKS_FOR_SLOT, PREAMBLE_MEMORY_LEN, TWEAKS_HASHING_USE_IV,
    TYPE1_BYTECODE_CLAIM_OFFSET, TYPE2_COMPONENT_HEADER_SIZE, TYPE2_MAX_COMPONENTS, build_input_data,
    bytecode_claim_output_from_point, compute_merkle_chunks_for_slot, compute_tweak_table,
    extract_bytecode_claim_from_input_data, extract_merkle_hint_blobs, get_aggregation_bytecode, hash_input_data,
    hash_pubkeys, run_bytecode_claims_reduction, unified_input_data_size_padded, xmss_aggregate,
    xmss_verify_aggregation,
};

/// Same message + slot, arbitrary set of pubkeys.
/// Built by recursively aggregating other type-1 multi-signatures and/or raw XMSS signatures.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct TypeOneInfo {
    pub message: [u8; 32],
    pub slot: u32,
    pub pubkeys: Vec<XmssPublicKey>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TypeOneMultiSignature {
    pub info: TypeOneInfo,
    pub proof: AggregatedXMSS,
}

/// A bundle of `n` type-1 multi-signatures with potentially distinct (message,
/// slot) per component, attested to by a single recursive SNARK.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TypeTwoMultiSignature {
    pub info: Vec<TypeOneInfo>,
    pub proof: AggregatedXMSS,
}

/// Deterministic encoding of a 32-byte message into [`MESSAGE_LEN_FE`] (= 8) KoalaBear elements.
/// Splits the input into 8 little-endian u32 chunks; each is reduced mod p.
pub fn message_bytes_to_field(message: &[u8; 32]) -> [F; MESSAGE_LEN_FE] {
    std::array::from_fn(|i| {
        let chunk: [u8; 4] = message[i * 4..i * 4 + 4].try_into().unwrap();
        F::new(u32::from_le_bytes(chunk))
    })
}

/// Build a type-1 multi-signature by aggregating `children` (recursive sub-proofs)
/// and `raw_signatures` (verified directly). All inputs must share `message` and `slot`.
pub fn aggregate_type_1(
    children: &[TypeOneMultiSignature],
    raw_signatures: Vec<(XmssPublicKey, XmssSignature)>,
    message: [u8; 32],
    slot: u32,
    log_inv_rate: usize,
) -> Result<TypeOneMultiSignature, ProverError> {
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

    let children_refs: Vec<(&[XmssPublicKey], AggregatedXMSS)> = children
        .iter()
        .map(|c| (c.info.pubkeys.as_slice(), c.proof.clone()))
        .collect();

    let message_fe = message_bytes_to_field(&message);
    let (pubkeys, aggregated) = xmss_aggregate(&children_refs, raw_signatures, &message_fe, slot, log_inv_rate)?;

    Ok(TypeOneMultiSignature {
        info: TypeOneInfo { message, slot, pubkeys },
        proof: aggregated,
    })
}

#[must_use]
pub fn verify_type1(sig: &TypeOneMultiSignature) -> bool {
    let message = message_bytes_to_field(&sig.info.message);
    xmss_verify_aggregation(&sig.info.pubkeys, &sig.proof, &message, sig.info.slot).is_ok()
}

/// Builds the type-2 outer public-input data buffer (zero-padded to the unified
/// size). The `bytecode_claim_output` slot is left empty here; it gets filled
/// in by the prover once the sumcheck reduction is complete, before hashing.
fn build_type2_input_data_skeleton(
    components: &[Type2Component],
    bytecode_claim_output: &[F],
    bytecode_hash: &[F; DIGEST_LEN],
) -> Vec<F> {
    let total = unified_input_data_size_padded(get_aggregation_bytecode().log_size());
    let mut data = vec![F::ZERO; total];

    // discriminator = 0  → type-2 mode
    // data[1] = n_components
    data[1] = F::from_usize(components.len());

    for (i, c) in components.iter().enumerate() {
        let off = TYPE2_HEADERS_OFFSET + i * TYPE2_COMPONENT_HEADER_SIZE;
        c.write_header(&mut data[off..off + TYPE2_COMPONENT_HEADER_SIZE]);
    }

    let claim_offset = TYPE2_HEADERS_OFFSET + TYPE2_MAX_COMPONENTS * TYPE2_COMPONENT_HEADER_SIZE;
    data[claim_offset..][..bytecode_claim_output.len()].copy_from_slice(bytecode_claim_output);

    let claim_padded = bytecode_claim_output.len().next_multiple_of(DIGEST_LEN);
    let domsep_offset = claim_offset + claim_padded;
    let domsep = poseidon16_compress_pair(bytecode_hash, &SNARK_DOMAIN_SEP);
    data[domsep_offset..][..DIGEST_LEN].copy_from_slice(&domsep);

    data
}

#[derive(Debug)]
struct Type2Component {
    n_sigs: usize,
    slice_hash: Digest,
    message_fe: [F; MESSAGE_LEN_FE],
    slot: u32,
    tweaks_hash: [F; DIGEST_LEN],
}

impl Type2Component {
    fn from_info(info: &TypeOneInfo) -> Self {
        let tweak_table = compute_tweak_table(info.slot);
        Self {
            n_sigs: info.pubkeys.len(),
            slice_hash: hash_pubkeys(&info.pubkeys),
            message_fe: message_bytes_to_field(&info.message),
            slot: info.slot,
            tweaks_hash: poseidon_compress_slice(&tweak_table, TWEAKS_HASHING_USE_IV),
        }
    }

    /// Write this component's header (n_sigs + slice_hash + message + merkle_chunks
    /// + tweaks_hash, total `TYPE2_COMPONENT_HEADER_SIZE` field elements) into `dst`.
    fn write_header(&self, dst: &mut [F]) {
        dst[0] = F::from_usize(self.n_sigs);
        dst[1..][..DIGEST_LEN].copy_from_slice(&self.slice_hash.0);
        dst[1 + DIGEST_LEN..][..MESSAGE_LEN_FE].copy_from_slice(&self.message_fe);
        dst[1 + DIGEST_LEN + MESSAGE_LEN_FE..][..N_MERKLE_CHUNKS_FOR_SLOT]
            .copy_from_slice(&compute_merkle_chunks_for_slot(self.slot));
        dst[1 + DIGEST_LEN + MESSAGE_LEN_FE + N_MERKLE_CHUNKS_FOR_SLOT..][..DIGEST_LEN]
            .copy_from_slice(&self.tweaks_hash);
    }
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
        n_components <= TYPE2_MAX_COMPONENTS,
        "merge_many_type_1: at most {TYPE2_MAX_COMPONENTS} components are supported"
    );
    let whir_config = lean_prover::default_whir_config(log_inv_rate);

    let bytecode = get_aggregation_bytecode();
    let bytecode_point_n_vars = bytecode.log_size() + log2_ceil_usize(N_INSTRUCTION_COLUMNS);
    let bytecode_claim_size = (bytecode_point_n_vars + 1) * DIMENSION;
    let claim_size_padded = bytecode_claim_size.next_multiple_of(DIGEST_LEN);

    let mut components: Vec<Type2Component> = Vec::with_capacity(n_components);
    let mut child_input_data: Vec<Vec<F>> = Vec::with_capacity(n_components);
    let mut child_bytecode_evals: Vec<Evaluation<EF>> = Vec::with_capacity(n_components);
    let mut child_raw_proofs: Vec<RawProof<F>> = Vec::with_capacity(n_components);

    for sig in &type_1_multi_signatures {
        assert!(sig.info.pubkeys.is_sorted(), "component pubkeys must be sorted");
        let component = Type2Component::from_info(&sig.info);

        let input_data = sig
            .proof
            .input_data(&sig.info.pubkeys, &component.message_fe, component.slot);
        let input_data_hash = hash_input_data(&input_data);
        let (verif, raw_proof) = verify_execution(bytecode, &input_data_hash, sig.proof.proof.clone())
            .expect("type-1 component proof failed to verify before type-2 merge");

        components.push(component);
        child_bytecode_evals.push(verif.bytecode_evaluation);
        child_input_data.push(input_data);
        child_raw_proofs.push(raw_proof);
    }

    let mut claims: Vec<Evaluation<EF>> = Vec::with_capacity(2 * n_components);
    for i in 0..n_components {
        let inner_claim = extract_bytecode_claim_from_input_data(
            &child_input_data[i][TYPE1_BYTECODE_CLAIM_OFFSET..],
            bytecode_point_n_vars,
        );
        claims.push(inner_claim);
        claims.push(child_bytecode_evals[i].clone());
    }

    let (claim_output, reduced_point, sumcheck_transcript) =
        run_bytecode_claims_reduction(&claims, bytecode, bytecode_point_n_vars, bytecode_claim_size);

    let pub_input_data = build_type2_input_data_skeleton(&components, &claim_output, &bytecode.hash);
    let public_input = hash_input_data(&pub_input_data).to_vec();

    let bytecode_value_hint_blobs: Vec<Vec<F>> = child_bytecode_evals
        .iter()
        .map(|eval| eval.value.as_basis_coefficients_slice().to_vec())
        .collect();

    let inner_bytecode_claim_blobs: Vec<Vec<F>> = child_input_data
        .iter()
        .map(|d| d[TYPE1_BYTECODE_CLAIM_OFFSET..][..claim_size_padded].to_vec())
        .collect();

    let proof_transcript_blobs: Vec<Vec<F>> = child_raw_proofs.iter().map(|p| p.transcript.clone()).collect();

    let (merkle_leaf_blobs, merkle_path_blobs) = extract_merkle_hint_blobs(&child_raw_proofs);

    let mut hints: HashMap<String, Vec<Vec<F>>> = HashMap::new();
    hints.insert("input_data".to_string(), vec![pub_input_data]);
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
    hints.insert("merkle_leaf".to_string(), merkle_leaf_blobs);
    hints.insert("merkle_path".to_string(), merkle_path_blobs);
    hints.insert("bytecode_sumcheck_proof".to_string(), vec![sumcheck_transcript]);

    let witness = ExecutionWitness {
        preamble_memory_len: PREAMBLE_MEMORY_LEN,
        hints,
    };
    let execution_proof = prove_execution(bytecode, &public_input, &witness, &whir_config, false)?;

    let aggregated = AggregatedXMSS {
        proof: execution_proof.proof,
        bytecode_point: Some(reduced_point),
        metadata: Some(execution_proof.metadata),
    };

    let info: Vec<TypeOneInfo> = type_1_multi_signatures.into_iter().map(|s| s.info).collect();
    Ok(TypeTwoMultiSignature {
        info,
        proof: aggregated,
    })
}

/// Verify a type-2 multi-signature: hash all per-component headers + the
/// reduced bytecode claim into a single public input digest, then verify the
/// SNARK proof against the unified bytecode.
#[must_use]
pub fn verify_type2(sig: &TypeTwoMultiSignature) -> bool {
    if sig.info.is_empty() || sig.info.len() > TYPE2_MAX_COMPONENTS {
        return false;
    }

    let bytecode = get_aggregation_bytecode();
    let bytecode_point_n_vars = bytecode.log_size() + log2_ceil_usize(N_INSTRUCTION_COLUMNS);
    let bytecode_claim_size = (bytecode_point_n_vars + 1) * DIMENSION;

    let Some(point) = &sig.proof.bytecode_point else {
        return false; // type-2 always carries a reduced bytecode point
    };
    let bytecode_claim_output = bytecode_claim_output_from_point(bytecode, point);
    debug_assert_eq!(bytecode_claim_output.len(), bytecode_claim_size);

    // n_sigs==0 and unsorted pubkeys both make verify_execution fail anyway
    // (the bytecode asserts the former, the slice_hash binds the latter), so
    // there's no need for fast-fail pre-checks here.
    let components: Vec<Type2Component> = sig.info.iter().map(Type2Component::from_info).collect();

    let pub_input_data = build_type2_input_data_skeleton(&components, &bytecode_claim_output, &bytecode.hash);
    let public_input = hash_input_data(&pub_input_data).to_vec();

    verify_execution(bytecode, &public_input, sig.proof.proof.clone()).is_ok()
}

/// Recover an independent type-1 multi-signature for the component at `index`
/// from a type-2 multi-signature. This is implemented by re-proving: the new
/// SNARK takes the OTHER components as witness hints, internally reconstructs
/// the type-2 outer hash and recursively verifies the type-2 SNARK, while
/// exposing a type-1 public input matching component `index`.
pub fn split_type_2(
    type_2_multi_signature: TypeTwoMultiSignature,
    index: usize,
    log_inv_rate: usize,
) -> Result<TypeOneMultiSignature, ProverError> {
    let n_components = type_2_multi_signature.info.len();
    assert!(index < n_components, "split index {index} out of bounds");
    assert!(
        n_components <= TYPE2_MAX_COMPONENTS,
        "split_type_2: at most {TYPE2_MAX_COMPONENTS} components are supported"
    );
    let whir_config = lean_prover::default_whir_config(log_inv_rate);

    let bytecode = get_aggregation_bytecode();
    let bytecode_point_n_vars = bytecode.log_size() + log2_ceil_usize(N_INSTRUCTION_COLUMNS);
    let bytecode_claim_size = (bytecode_point_n_vars + 1) * DIMENSION;
    let claim_size_padded = bytecode_claim_size.next_multiple_of(DIGEST_LEN);

    let components: Vec<Type2Component> = type_2_multi_signature
        .info
        .iter()
        .map(Type2Component::from_info)
        .collect();

    let type2_point = type_2_multi_signature
        .proof
        .bytecode_point
        .as_ref()
        .expect("type-2 proof must carry a reduced bytecode_point");
    let type2_bytecode_claim_output = bytecode_claim_output_from_point(bytecode, type2_point);
    debug_assert_eq!(type2_bytecode_claim_output.len(), bytecode_claim_size);

    let type2_input_data = build_type2_input_data_skeleton(&components, &type2_bytecode_claim_output, &bytecode.hash);
    let type2_input_data_hash = hash_input_data(&type2_input_data);
    let (verif, raw_proof) = verify_execution(
        bytecode,
        &type2_input_data_hash,
        type_2_multi_signature.proof.proof.clone(),
    )
    .expect("type-2 proof failed to verify before split");

    // Reduce the type-2's forwarded inner claim + the outer recursion eval.
    let inner_claim =
        extract_bytecode_claim_from_input_data(&type2_input_data[TYPE2_BYTECODE_CLAIM_OFFSET..], bytecode_point_n_vars);
    let bytecode_value_hint_blob: Vec<F> = verif.bytecode_evaluation.value.as_basis_coefficients_slice().to_vec();
    let claims = vec![inner_claim, verif.bytecode_evaluation];

    let (claim_output, reduced_point, sumcheck_transcript) =
        run_bytecode_claims_reduction(&claims, bytecode, bytecode_point_n_vars, bytecode_claim_size);

    // Outer (split) public input: type-1 layout for the kept component.
    let mut info = type_2_multi_signature.info;
    let kept_info = info.swap_remove(index);
    let kept = &components[index];
    let pub_input_data = build_input_data(
        kept.n_sigs,
        &kept.slice_hash.0,
        &kept.message_fe,
        kept.slot,
        &kept.tweaks_hash,
        &claim_output,
        &bytecode.hash,
    );
    let public_input = hash_input_data(&pub_input_data).to_vec();

    let tweak_table = compute_tweak_table(kept.slot);

    let mut type2_components_blob: Vec<F> = vec![F::ZERO; TYPE2_MAX_COMPONENTS * TYPE2_COMPONENT_HEADER_SIZE];
    for (i, c) in components.iter().enumerate() {
        let off = i * TYPE2_COMPONENT_HEADER_SIZE;
        c.write_header(&mut type2_components_blob[off..off + TYPE2_COMPONENT_HEADER_SIZE]);
    }

    let type2_inner_bytecode_claim: Vec<F> =
        type2_input_data[TYPE2_BYTECODE_CLAIM_OFFSET..][..claim_size_padded].to_vec();

    let (merkle_leaf_blobs, merkle_path_blobs) = extract_merkle_hint_blobs(std::slice::from_ref(&raw_proof));
    let proof_transcript = raw_proof.transcript;
    let proof_transcript_size = vec![F::from_usize(proof_transcript.len())];

    let mut hints: HashMap<String, Vec<Vec<F>>> = HashMap::new();
    hints.insert("input_data".to_string(), vec![pub_input_data]);
    // [n_recursions=1, n_dup=0, pubkeys_len=0, n_raw_xmss=0]
    hints.insert("meta".to_string(), vec![vec![F::ONE, F::ZERO, F::ZERO, F::ZERO]]);
    hints.insert("pubkeys".to_string(), vec![Vec::<F>::new()]);
    hints.insert("raw_indices".to_string(), vec![Vec::<F>::new()]);
    // aggregate_sizes is hint-consumed before the fast-path branch, but its value is unused there.
    hints.insert("aggregate_sizes".to_string(), vec![vec![F::ONE]]);
    hints.insert("sub_indices".to_string(), Vec::new());
    hints.insert("wots".to_string(), Vec::new());
    hints.insert("xmss_merkle_node".to_string(), Vec::new());
    hints.insert("tweak_table".to_string(), vec![tweak_table]);
    hints.insert("is_inner_type2".to_string(), vec![vec![F::ONE]]);
    hints.insert(
        "type2_meta".to_string(),
        vec![vec![F::from_usize(n_components), F::from_usize(index)]],
    );
    hints.insert("type2_components".to_string(), vec![type2_components_blob]);
    hints.insert("inner_bytecode_claim".to_string(), vec![type2_inner_bytecode_claim]);
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
        proof: AggregatedXMSS {
            proof: execution_proof.proof,
            bytecode_point: Some(reduced_point),
            metadata: Some(execution_proof.metadata),
        },
    })
}
