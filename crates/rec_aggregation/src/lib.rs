#![cfg_attr(not(test), allow(unused_crate_dependencies))]
use lean_prover::prove_execution::prove_execution;
use lean_prover::verify_execution::verify_execution;
use lean_prover::{default_whir_config, verify_execution::ProofVerificationDetails};
use lean_vm::*;
use multilinear_toolkit::prelude::*;
use tracing::instrument;
use utils::{build_prover_state, poseidon_compress_slice, poseidon16_compress_pair};
use xmss::{LOG_LIFETIME, MESSAGE_LEN_FE, SIG_SIZE_FE, XmssPublicKey, XmssSignature, slot_to_field_elements};

use crate::compilation::get_aggregation_bytecode;

pub mod benchmark;
pub(crate) mod compilation;

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

pub fn slice_hash_pubkeys(pub_keys: &[[F; DIGEST_LEN]]) -> [F; DIGEST_LEN] {
    let flat: Vec<F> = pub_keys.iter().flat_map(|pk| pk.iter().copied()).collect();
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

#[derive(Debug)]
pub struct AggregatedSigs {
    pub pub_keys: Vec<[F; DIGEST_LEN]>,
    pub proof: Vec<F>,
    pub compressed_proof_len_fe: usize,
    pub bytecode_point: Option<MultilinearPoint<EF>>,
    pub metadata: ExecutionMetadata,
}

impl AggregatedSigs {
    pub fn public_input(&self, message: &[F; MESSAGE_LEN_FE], slot: u32, proximity_gaps_conjecture: bool) -> Vec<F> {
        let bytecode = get_aggregation_bytecode(proximity_gaps_conjecture);
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

        let slice_hash = slice_hash_pubkeys(&self.pub_keys);

        build_non_reserved_public_input(self.pub_keys.len(), &slice_hash, message, slot, &bytecode_claim_output)
    }
}

pub fn verify_aggregation(
    sigs: &AggregatedSigs,
    message: &[F; MESSAGE_LEN_FE],
    slot: u32,
    log_inv_rate: usize,
    prox_gaps_conjecture: bool,
) -> Result<ProofVerificationDetails, ProofError> {
    let public_input = sigs.public_input(&message, slot, prox_gaps_conjecture);
    let bytecode = get_aggregation_bytecode(prox_gaps_conjecture);
    verify_execution(
        bytecode,
        &public_input,
        sigs.proof.clone(),
        default_whir_config(log_inv_rate, prox_gaps_conjecture),
    )
}

#[allow(clippy::too_many_arguments)]
#[instrument(skip_all)]
pub fn aggregate(
    children: &[AggregatedSigs],
    raw_signers: &[(XmssPublicKey, XmssSignature)],
    message: &[F; MESSAGE_LEN_FE],
    slot: u32,
    overlap: usize,
    log_inv_rate: usize,
    prox_gaps_conjecture: bool,
    tracing: bool,
) -> AggregatedSigs {
    let n_recursions = children.len();
    let raw_count = raw_signers.len();
    let whir_config = default_whir_config(log_inv_rate, prox_gaps_conjecture);

    let bytecode = get_aggregation_bytecode(prox_gaps_conjecture);
    let bytecode_point_n_vars = bytecode.log_size() + log2_ceil_usize(N_INSTRUCTION_COLUMNS);
    let bytecode_claim_size = (bytecode_point_n_vars + 1) * DIMENSION;

    // Build global pub_keys: raw ++ children (with overlap dedup)
    let raw_pub_keys: Vec<[F; DIGEST_LEN]> = raw_signers.iter().map(|(pk, _)| pk.merkle_root).collect();
    let mut global_pub_keys = raw_pub_keys;
    for (i, child) in children.iter().enumerate() {
        if i == 0 {
            global_pub_keys.extend_from_slice(&child.pub_keys);
        } else {
            global_pub_keys.extend_from_slice(&child.pub_keys[overlap..]);
        }
    }
    let n_sigs = global_pub_keys.len();

    // Build dup pub_keys (overlap portions of children 1+)
    let mut dup_pub_keys: Vec<[F; DIGEST_LEN]> = Vec::new();
    for (i, child) in children.iter().enumerate() {
        if i > 0 && overlap > 0 {
            dup_pub_keys.extend_from_slice(&child.pub_keys[..overlap]);
        }
    }
    let n_dup = dup_pub_keys.len();

    // Verify child proofs
    let mut child_pub_inputs: Vec<Vec<F>> = vec![];
    let mut child_bytecode_evals: Vec<Evaluation<EF>> = vec![];
    for child in children {
        let child_pub_input = child.public_input(message, slot, prox_gaps_conjecture);
        let verif = verify_execution(bytecode, &child_pub_input, child.proof.clone(), whir_config.clone()).unwrap();
        child_bytecode_evals.push(verif.bytecode_evaluation);
        child_pub_inputs.push(child_pub_input);
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
            1,
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

        (claim_output, Some(reduced_point), reduction_prover.raw_proof())
    } else {
        let mut claim_output = vec![F::ZERO; bytecode_claim_size];
        claim_output[bytecode_point_n_vars * DIMENSION] = bytecode.instructions_multilinear[0];
        (claim_output, None, vec![])
    };

    // Build public input
    let slice_hash = slice_hash_pubkeys(&global_pub_keys);
    let non_reserved_public_input =
        build_non_reserved_public_input(n_sigs, &slice_hash, message, slot, &bytecode_claim_output);
    let public_memory = build_public_memory(&non_reserved_public_input);

    // Build private input
    // Layout: [n_recursions, n_dup, ptr_pubkeys, ptr_source_0..n_recursions, ptr_bytecode_sumcheck,
    //          global_pubkeys, dup_pubkeys, source_blocks..., bytecode_sumcheck_proof]
    let header_size = n_recursions + 5;
    let pubkeys_start = public_memory.len() + header_size;
    let pubkeys_block_size = n_sigs * DIGEST_LEN + n_dup * DIGEST_LEN;

    // Build source blocks
    let mut source_blocks: Vec<Vec<F>> = vec![];

    // Source 0: raw XMSS
    {
        let mut block = vec![];
        block.push(F::from_usize(raw_count));
        for i in 0..raw_count {
            block.push(F::from_usize(i));
        }
        for (_, sig) in raw_signers {
            block.extend(encode_xmss_signature(sig));
        }
        source_blocks.push(block);
    }

    // Sources 1..n_recursions: recursive children
    let mut child_global_start = raw_count;
    for (i, child) in children.iter().enumerate() {
        let mut block = vec![];
        let child_count = child.pub_keys.len();

        block.push(F::from_usize(child_count));
        // For children after the first, the overlap portion uses dup indices
        if i > 0 && overlap > 0 {
            let dup_offset = n_sigs + (i - 1) * overlap;
            for j in 0..overlap {
                block.push(F::from_usize(dup_offset + j));
            }
        }
        let non_overlap_count = if i > 0 { child_count - overlap } else { child_count };
        for j in 0..non_overlap_count {
            block.push(F::from_usize(child_global_start + j));
        }

        // bytecode_value_hint (DIM elements)
        block.extend_from_slice(child_bytecode_evals[i].value.as_basis_coefficients_slice());
        // inner_pub_mem
        let child_pub_mem = build_public_memory(&child_pub_inputs[i]);
        block.extend_from_slice(&child_pub_mem);
        // proof_transcript
        block.extend_from_slice(&child.proof);

        source_blocks.push(block);
        child_global_start += non_overlap_count;
    }

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
        private_input.extend_from_slice(pk);
    }
    for pk in &dup_pub_keys {
        private_input.extend_from_slice(pk);
    }
    for block in &source_blocks {
        private_input.extend_from_slice(block);
    }
    private_input.extend_from_slice(&final_sumcheck_transcript);

    let execution_proof = prove_execution(
        bytecode,
        (&non_reserved_public_input, &private_input),
        &vec![],
        &whir_config,
        false,
    );

    if tracing {
        println!("{}", execution_proof.metadata.display());
    }

    AggregatedSigs {
        pub_keys: global_pub_keys,
        proof: execution_proof.proof,
        compressed_proof_len_fe: execution_proof.proof_size_fe,
        bytecode_point,
        metadata: execution_proof.metadata,
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
