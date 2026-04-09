#![cfg_attr(not(test), allow(unused_crate_dependencies))]
use backend::*;
use lean_prover::SNARK_DOMAIN_SEP;
use lean_prover::prove_execution::prove_execution;
use lean_prover::verify_execution::ProofVerificationDetails;
use lean_prover::verify_execution::verify_execution;
use lean_vm::*;
use tracing::instrument;
use utils::{build_prover_state, get_poseidon16, poseidon_compress_slice, poseidon16_compress_pair};
use xmss::{LOG_LIFETIME, MESSAGE_LEN_FE, PUB_KEY_FLAT_SIZE, V, W, WOTS_SIG_SIZE_FE, XmssPublicKey, XmssSignature};

use serde::{Deserialize, Serialize};
use std::collections::HashSet;

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

/// Number of tweaks in the table: 1 encoding + V*CHAIN_LENGTH chains + (V-1) wots_pk + LOG_LIFETIME merkle
const N_TWEAKS: usize = 1 + V * CHAIN_LENGTH + (V - 1) + LOG_LIFETIME;
/// Each tweak is stored as a 5-FE slot [0, tw[0], tw[1], 0, 0] so that we can use copy_5
const TWEAK_SLOT_SIZE: usize = 5;
const TWEAK_TABLE_SIZE_FE_PADDED: usize = (N_TWEAKS * TWEAK_SLOT_SIZE).next_multiple_of(DIGEST_LEN);

const TWEAKS_HASHING_USE_IV: bool = false; // fixed size → no IV needed

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Digest(pub [F; DIGEST_LEN]);

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

/// Each tweak is stored as a 5-FE slot: [0, tw[0], tw[1], 0, 0]
fn compute_tweak_table(slot: u32) -> Vec<F> {
    let mut table = Vec::new();

    let push_padded = |table: &mut Vec<F>, tweak_type: usize, sub_position: usize, index: u32| {
        let tw = make_tweak_values(tweak_type, sub_position, index);
        table.push(F::ZERO);
        table.push(tw[0]);
        table.push(tw[1]);
        table.push(F::ZERO);
        table.push(F::ZERO);
    };

    // Encoding tweak
    push_padded(&mut table, TWEAK_TYPE_ENCODING, 0, slot);

    // Chain tweaks: for chain i, step s → make_tweak(CHAIN, i*CHAIN_LENGTH + s, slot)
    for i in 0..V {
        for s in 0..CHAIN_LENGTH {
            push_padded(&mut table, TWEAK_TYPE_CHAIN, i * CHAIN_LENGTH + s, slot);
        }
    }

    // WOTS_PK tweaks: for sub_pos p = 0..V-2
    for p in 0..V - 1 {
        push_padded(&mut table, TWEAK_TYPE_WOTS_PK, p, slot);
    }

    // Merkle tweaks: for level 0..LOG_LIFETIME-1
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

fn build_non_reserved_public_input(
    n_sigs: usize,
    slice_hash: &[F; DIGEST_LEN],
    message: &[F; MESSAGE_LEN_FE],
    slot: u32,
    tweaks_hash: &[F; DIGEST_LEN],
    bytecode_claim_output: &[F],
    bytecode_hash: &[F; DIGEST_LEN],
) -> Vec<F> {
    let mut pi = vec![];
    pi.push(F::from_usize(n_sigs));
    pi.extend_from_slice(slice_hash);
    pi.extend_from_slice(message);
    pi.push(F::from_usize((slot & 0xFFFF) as usize));
    pi.push(F::from_usize(((slot >> 16) & 0xFFFF) as usize));
    pi.extend(compute_merkle_chunks_for_slot(slot));
    pi.extend_from_slice(tweaks_hash);
    pi.extend_from_slice(bytecode_claim_output);
    pi.extend(std::iter::repeat_n(
        F::ZERO,
        bytecode_claim_output.len().next_multiple_of(DIGEST_LEN) - bytecode_claim_output.len(),
    ));
    pi.extend_from_slice(&poseidon16_compress_pair(bytecode_hash, &SNARK_DOMAIN_SEP));
    pi
}

fn encode_wots_signature(sig: &XmssSignature) -> Vec<F> {
    // The in-memory signature buffer consumed by `hint_wots` is just the WOTS part:
    // `randomness | chain_tips`. The XMSS merkle path is delivered out-of-band via
    // `hint_xmss_merkle_node`, see `encode_xmss_merkle_path`.
    let mut data = vec![];
    data.extend(sig.wots_signature.randomness.to_vec());
    data.extend(sig.wots_signature.chain_tips.iter().flat_map(|digest| digest.to_vec()));
    assert_eq!(data.len(), WOTS_SIG_SIZE_FE);
    data
}

/// Flatten the merkle path of an XMSS signature into a 4*LOG_LIFETIME flat vec, in the
/// order it will be consumed by successive `hint_xmss_merkle_node` calls inside
/// `do_4_merkle_levels` (= the natural leaf-to-root order of the merkle path).
fn encode_xmss_merkle_path(sig: &XmssSignature) -> Vec<F> {
    sig.merkle_proof.iter().flat_map(|d| d.to_vec()).collect()
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

    pub fn public_input(&self, pub_keys: &[XmssPublicKey], message: &[F; MESSAGE_LEN_FE], slot: u32) -> Vec<F> {
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

        build_non_reserved_public_input(
            pub_keys.len(),
            &slice_hash.0,
            message,
            slot,
            &tweaks_hash,
            &bytecode_claim_output,
            &bytecode.hash,
        )
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
    let public_input = agg_sig.public_input(pub_keys, message, slot);
    let bytecode = get_aggregation_bytecode();
    verify_execution(bytecode, &public_input, agg_sig.proof.clone()).map(|(details, _)| details)
}

/// panics if one of the sub-proof (children) is invalid
#[instrument(skip_all)]
pub fn xmss_aggregate(
    children: &[(&[XmssPublicKey], AggregatedXMSS)],
    mut raw_xmss: Vec<(XmssPublicKey, XmssSignature)>,
    message: &[F; MESSAGE_LEN_FE],
    slot: u32,
    log_inv_rate: usize,
) -> (Vec<XmssPublicKey>, AggregatedXMSS) {
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
    let mut child_pub_inputs = vec![];
    let mut child_bytecode_evals = vec![];
    let mut child_raw_proofs = vec![];
    for (child_pub_keys, child) in children {
        let child_pub_input = child.public_input(child_pub_keys, message, slot);
        let (verif, raw_proof) = verify_execution(bytecode, &child_pub_input, child.proof.clone()).unwrap();
        child_bytecode_evals.push(verif.bytecode_evaluation);
        child_pub_inputs.push(child_pub_input);
        child_raw_proofs.push(raw_proof);
    }

    // Bytecode sumcheck reduction
    let (bytecode_claim_output, bytecode_point, final_sumcheck_transcript) = if n_recursions > 0 {
        let bytecode_claim_offset = 1 + DIGEST_LEN + 2 + MESSAGE_LEN_FE + N_MERKLE_CHUNKS_FOR_SLOT + DIGEST_LEN;
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
        &slice_hash.0,
        message,
        slot,
        &tweaks_hash,
        &bytecode_claim_output,
        &bytecode.hash,
    );
    let public_memory = build_public_memory(&non_reserved_public_input);

    // Build private input
    // Layout: [tweak_table (FIXED size, sits at the FIXED address public_memory.len() so the
    //          .py code can address it via the TWEAK_TABLE_ADDR compile-time constant),
    //          n_recursions, n_dup, ptr_pubkeys, ptr_source_0..n_recursions, ptr_bytecode_sumcheck,
    //          global_pubkeys, dup_pubkeys, source_blocks..., bytecode_sumcheck_proof]
    //
    // We dropped `ptr_tweak_table` from the header because the address is now a
    // compile-time constant; main.py reads tweak_table = TWEAK_TABLE_ADDR directly.
    let tweak_table_ptr = public_memory.len();
    let header_size = n_recursions + 5;
    let header_start = tweak_table_ptr + TWEAK_TABLE_SIZE_FE_PADDED;
    let pubkeys_start = header_start + header_size;

    // Build source blocks (also discovers duplicate pub_keys)
    let mut claimed: HashSet<XmssPublicKey> = HashSet::new();
    let mut dup_pub_keys: Vec<XmssPublicKey> = Vec::new();
    let mut source_blocks: Vec<Vec<F>> = vec![];

    // Build the WOTS-portion signature buffers (one Vec<F> per signature, consumed by
    // hint_wots). The merkle path of each sig is delivered separately via
    // hint_xmss_merkle_node; we flatten it here in the order it will be consumed at
    // runtime.
    let wots_signatures: Vec<Vec<F>> = raw_xmss.iter().map(|(_, sig)| encode_wots_signature(sig)).collect();
    let xmss_merkle_nodes: Vec<F> = raw_xmss
        .iter()
        .flat_map(|(_, sig)| encode_xmss_merkle_path(sig))
        .collect();

    // Source 0: raw XMSS (indices only; signature data goes via hint_wots)
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
    for (i, (child_pub_keys, _child)) in children.iter().enumerate() {
        let mut block = vec![F::from_usize(child_pub_keys.len())];
        for key in *child_pub_keys {
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
    let pubkeys_block_size = n_sigs * PUB_KEY_FLAT_SIZE + n_dup * PUB_KEY_FLAT_SIZE;

    // Compute absolute memory addresses for each source block (placed after the pubkeys block).
    let sources_start = pubkeys_start + pubkeys_block_size;
    let mut offset = sources_start;
    let mut source_ptrs: Vec<usize> = vec![];
    for block in &source_blocks {
        source_ptrs.push(offset);
        offset += block.len();
    }
    let bytecode_sumcheck_proof_ptr = offset;

    // Tweak table sits at the very start of private input (FIXED address).
    let mut private_input: Vec<F> = Vec::with_capacity(TWEAK_TABLE_SIZE_FE_PADDED);
    private_input.extend_from_slice(&tweak_table);
    assert_eq!(private_input.len(), TWEAK_TABLE_SIZE_FE_PADDED);

    // Header (variable-length only via n_recursions; lives right after the tweak table).
    private_input.push(F::from_usize(n_recursions));
    private_input.push(F::from_usize(n_dup));
    private_input.push(F::from_usize(pubkeys_start));
    for &ptr in &source_ptrs {
        private_input.push(F::from_usize(ptr));
    }
    private_input.push(F::from_usize(bytecode_sumcheck_proof_ptr));
    assert_eq!(private_input.len(), TWEAK_TABLE_SIZE_FE_PADDED + header_size);

    // Pubkeys block.
    for pk in &global_pub_keys {
        private_input.extend_from_slice(&pk.flaten());
    }
    for pk in &dup_pub_keys {
        private_input.extend_from_slice(&pk.flaten());
    }
    // Source blocks (already addressed by source_ptrs above).
    for block in &source_blocks {
        private_input.extend_from_slice(block);
    }
    private_input.extend_from_slice(&final_sumcheck_transcript);

    // Build Merkle paths from all child proofs (one Vec<F> per hint_merkle call in whir.py)
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
        wots_signatures: &wots_signatures,
        xmss_merkle_nodes: &xmss_merkle_nodes,
        merkle_paths: &merkle_paths,
    };
    let execution_proof = prove_execution(bytecode, &non_reserved_public_input, &witness, &whir_config, false);

    (
        global_pub_keys,
        AggregatedXMSS {
            proof: execution_proof.proof,
            bytecode_point,
            metadata: Some(execution_proof.metadata),
        },
    )
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
