#![cfg_attr(not(test), allow(unused_crate_dependencies))]
use lean_prover::default_whir_config;
use lean_prover::prove_execution::prove_execution;
use lean_prover::verify_execution::verify_execution;
use lean_vm::*;
use multilinear_toolkit::prelude::*;
use tracing::instrument;
use utils::{bit_reverse, build_prover_state, poseidon_compress_slice, poseidon16_compress_pair};
use xmss::{LOG_LIFETIME, MESSAGE_LEN_FE, SIG_SIZE_FE, XmssPublicKey, XmssSignature, slot_to_field_elements};

pub mod benchmark;
pub(crate) mod compilation;

pub const LOG_SIZE_PUBKEY_REGISTRY: usize = 14;
const MERKLE_LEVELS_PER_CHUNK_FOR_SLOT: usize = 4;
const N_MERKLE_CHUNKS_FOR_SLOT: usize = LOG_LIFETIME / MERKLE_LEVELS_PER_CHUNK_FOR_SLOT;

#[derive(Debug, Clone)]
pub struct AggregationTopology {
    pub raw_xmss: usize,
    pub children: Vec<AggregationTopology>,
}

pub(crate) fn count_signers(topology: &AggregationTopology, overlap: usize) -> usize {
    let child_count: usize = topology.children.iter().map(|c| count_signers(c, overlap)).sum();
    let n_overlaps = topology.children.len().saturating_sub(1);
    topology.raw_xmss + child_count - overlap * n_overlaps
}

/// layers[0] = leaves, layers[height] = [root].
pub(crate) fn build_registry_merkle_tree(signers: &[(usize, [F; DIGEST_LEN])]) -> Vec<Vec<[F; DIGEST_LEN]>> {
    let height = LOG_SIZE_PUBKEY_REGISTRY;
    let n_leaves = 1 << height;

    // Initialize all leaves as zero hash
    let mut leaves = vec![[F::ZERO; DIGEST_LEN]; n_leaves];

    // Place each signer at the bit-reversed position
    for &(index, ref digest) in signers {
        let pos = bit_reverse(index, height);
        leaves[pos] = *digest;
    }

    // Build tree bottom-up
    let mut layers = vec![leaves];
    for level in 0..height {
        let prev = &layers[level];
        let n_nodes = prev.len() / 2;
        let mut current = Vec::with_capacity(n_nodes);
        for i in 0..n_nodes {
            current.push(poseidon16_compress_pair(prev[2 * i], prev[2 * i + 1]));
        }
        layers.push(current);
    }
    layers
}

fn get_merkle_proof(layers: &[Vec<[F; DIGEST_LEN]>], signer_index: usize) -> Vec<[F; DIGEST_LEN]> {
    let height = layers.len() - 1;
    let mut pos = bit_reverse(signer_index, height);
    let mut proof = Vec::with_capacity(height);
    for layer in layers.iter().take(height) {
        let sibling_pos = pos ^ 1;
        proof.push(layer[sibling_pos]);
        pos >>= 1;
    }
    proof
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
    registry_root: &[F; DIGEST_LEN],
    signer_indexes_hash: &[F; DIGEST_LEN],
    message: &[F; MESSAGE_LEN_FE],
    slot: u32,
    bytecode_claim_output: &[F],
) -> Vec<F> {
    let mut pi = vec![];
    pi.push(F::from_usize(n_sigs));
    pi.extend_from_slice(registry_root);
    pi.extend_from_slice(signer_indexes_hash);
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
    pub signer_indices: Vec<usize>,
    pub proof: Vec<F>,
    pub bytecode_point: Option<MultilinearPoint<EF>>,
}

impl AggregatedSigs {
    pub fn public_input(
        &self,
        registry_root: &[F; DIGEST_LEN],
        message: &[F; MESSAGE_LEN_FE],
        slot: u32,
        bytecode: &Bytecode,
    ) -> Vec<F> {
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

        let indices_fe: Vec<F> = self.signer_indices.iter().map(|&i| F::from_usize(i)).collect();
        let signer_indexes_hash = poseidon_compress_slice(&indices_fe);

        build_non_reserved_public_input(
            self.signer_indices.len(),
            registry_root,
            &signer_indexes_hash,
            message,
            slot,
            &bytecode_claim_output,
        )
    }
}

#[allow(clippy::too_many_arguments)]
#[instrument(skip_all)]
pub fn aggregate_merge(
    children: &[AggregatedSigs],
    raw_signers: &[(usize, XmssPublicKey, XmssSignature)],
    message: &[F; MESSAGE_LEN_FE],
    slot: u32,
    registry_merkle_tree: &[Vec<[F; DIGEST_LEN]>],
    bytecode: &Bytecode,
    overlap: usize,
    log_inv_rate: usize,
    prox_gaps_conjecture: bool,
    tracing: bool,
) -> AggregatedSigs {
    let n_recursions = children.len();
    let raw_count = raw_signers.len();
    let whir_config = default_whir_config(log_inv_rate, prox_gaps_conjecture);
    let registry_root = &registry_merkle_tree.last().unwrap()[0];

    let bytecode_point_n_vars = bytecode.log_size() + log2_ceil_usize(N_INSTRUCTION_COLUMNS);
    let bytecode_claim_size = (bytecode_point_n_vars + 1) * DIMENSION;

    // Build merged signer_indices: raw ++ children with overlap
    let raw_indices: Vec<usize> = raw_signers.iter().map(|(idx, _, _)| *idx).collect();
    let mut signer_indices = raw_indices.clone();
    for (i, child) in children.iter().enumerate() {
        if i == 0 {
            signer_indices.extend_from_slice(&child.signer_indices);
        } else {
            signer_indices.extend_from_slice(&child.signer_indices[overlap..]);
        }
    }
    let n_sigs = signer_indices.len();

    // Verify child proofs
    let mut child_pub_inputs: Vec<Vec<F>> = vec![];
    let mut child_bytecode_evals: Vec<Evaluation<EF>> = vec![];
    for child in children {
        let child_pub_input = child.public_input(registry_root, message, slot, bytecode);
        let verif = verify_execution(bytecode, &child_pub_input, child.proof.clone(), whir_config.clone()).unwrap();
        child_bytecode_evals.push(verif.bytecode_evaluation);
        child_pub_inputs.push(child_pub_input);
    }

    // Sub-index lists and dup indices
    let mut all_sub_indices: Vec<&[usize]> = vec![&raw_indices];
    let mut dup_indices = Vec::new();
    for (i, child) in children.iter().enumerate() {
        all_sub_indices.push(&child.signer_indices);
        if i > 0 && overlap > 0 {
            dup_indices.extend_from_slice(&child.signer_indices[..overlap]);
        }
    }
    dup_indices.sort();

    // Bytecode sumcheck reduction
    let (bytecode_claim_output, bytecode_point, final_sumcheck_transcript) = if n_recursions > 0 {
        let bytecode_claim_offset = 1 + 2 * DIGEST_LEN + 2 + MESSAGE_LEN_FE + N_MERKLE_CHUNKS_FOR_SLOT;
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
    let global_indices_fe: Vec<F> = signer_indices.iter().map(|&i| F::from_usize(i)).collect();
    let signer_indexes_hash = poseidon_compress_slice(&global_indices_fe);
    let non_reserved_public_input = build_non_reserved_public_input(
        n_sigs,
        registry_root,
        &signer_indexes_hash,
        message,
        slot,
        &bytecode_claim_output,
    );
    let public_memory = build_public_memory(&non_reserved_public_input);

    // header: 1 n_recursions + (n_recursions+1) pointers + 1 sumcheck_proof_ptr + 1 n_dup + n_sigs + n_dup
    let header_size = 1 + (n_recursions + 1) + 1 + 1 + n_sigs + dup_indices.len();

    let mut source_blocks: Vec<Vec<F>> = vec![];

    // Source 0: raw XMSS
    {
        let mut block = vec![];
        block.push(F::from_usize(raw_count));
        for &(idx, _, _) in raw_signers {
            block.push(F::from_usize(idx));
        }
        for (idx, pk, sig) in raw_signers {
            block.extend_from_slice(&pk.merkle_root);
            let proof = get_merkle_proof(registry_merkle_tree, *idx);
            for sibling in &proof {
                block.extend_from_slice(sibling);
            }
            block.extend(encode_xmss_signature(sig));
        }
        source_blocks.push(block);
    }

    // Sources 1..n_recursions: recursive children
    for (i, child) in children.iter().enumerate() {
        let mut block = vec![];
        let sub_indices = all_sub_indices[i + 1];

        block.push(F::from_usize(sub_indices.len()));
        for &idx in sub_indices {
            block.push(F::from_usize(idx));
        }
        // bytecode_value_hint (DIM elements)
        block.extend_from_slice(child_bytecode_evals[i].value.as_basis_coefficients_slice());
        // inner_pub_mem
        let child_pub_mem = build_public_memory(&child_pub_inputs[i]);
        block.extend_from_slice(&child_pub_mem);
        // proof_transcript
        block.extend_from_slice(&child.proof);

        source_blocks.push(block);
    }

    // Compute absolute memory addresses for each source block
    let mut offset_in_priv = header_size;
    let mut source_ptrs: Vec<usize> = vec![];
    for block in &source_blocks {
        source_ptrs.push(public_memory.len() + offset_in_priv);
        offset_in_priv += block.len();
    }
    let bytecode_sumcheck_proof_ptr = public_memory.len() + offset_in_priv;

    let mut private_input = vec![];
    private_input.push(F::from_usize(n_recursions));
    for &ptr in &source_ptrs {
        private_input.push(F::from_usize(ptr));
    }
    private_input.push(F::from_usize(bytecode_sumcheck_proof_ptr));
    private_input.push(F::from_usize(dup_indices.len()));
    for &idx in &signer_indices {
        private_input.push(F::from_usize(idx));
    }
    for &idx in &dup_indices {
        private_input.push(F::from_usize(idx));
    }
    assert_eq!(private_input.len(), header_size);

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
        println!("{}", execution_proof.exec_summary);
    }

    AggregatedSigs {
        signer_indices,
        proof: execution_proof.proof,
        bytecode_point,
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
