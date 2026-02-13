#![cfg_attr(not(test), allow(unused_crate_dependencies))]
use std::time::Instant;

use lean_prover::default_whir_config;
use lean_prover::prove_execution::prove_execution;
use lean_prover::verify_execution::verify_execution;
use lean_vm::*;
use multilinear_toolkit::prelude::*;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use tracing::instrument;
use utils::{bit_reverse, build_prover_state, poseidon_compress_slice, poseidon16_compress_pair};
use xmss::{LOG_LIFETIME, MESSAGE_LEN_FE, SIG_SIZE_FE, XmssPublicKey, XmssSignature, slot_to_field_elements};

use crate::compilation::compile_main_program_self_referential;

pub(crate) mod compilation;

pub const LOG_SIZE_PUBKEY_REGISTRY: usize = 14;
const MERKLE_LEVELS_PER_CHUNK_FOR_SLOT: usize = 4;
const N_MERKLE_CHUNKS_FOR_SLOT: usize = LOG_LIFETIME / MERKLE_LEVELS_PER_CHUNK_FOR_SLOT;

#[derive(Debug, Clone)]
pub struct AggregationTopology {
    pub raw: usize,
    pub profile: bool,
    pub children: Vec<AggregationTopology>,
}

fn count_signers(topology: &AggregationTopology, overlap: usize) -> usize {
    let child_count: usize = topology.children.iter().map(|c| count_signers(c, overlap)).sum();
    let n_overlaps = topology.children.len().saturating_sub(1);
    topology.raw + child_count - overlap * n_overlaps
}

/// layers[0] = leaves, layers[height] = [root].
fn build_registry_merkle_tree(signers: &[(usize, [F; DIGEST_LEN])]) -> Vec<Vec<[F; DIGEST_LEN]>> {
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
    n_recursions: usize,
    registry_root: &[F; DIGEST_LEN],
    signer_indexes_hash: &[F; DIGEST_LEN],
    message: &[F; MESSAGE_LEN_FE],
    slot: u32,
    bytecode_claim_output: &[F],
) -> Vec<F> {
    let mut pi = vec![];
    pi.push(F::from_usize(n_sigs));
    pi.push(F::from_usize(n_recursions));
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

struct ChildProofData {
    proof: Vec<F>,
    public_input: Vec<F>,
    bytecode_evaluation: Evaluation<EF>,
}

#[allow(clippy::too_many_arguments)]
#[instrument(skip_all)]
fn prove_aggregation_node(
    topology: &AggregationTopology,
    bytecode: &Bytecode,
    message: &[F; MESSAGE_LEN_FE],
    slot: u32,
    registry_merkle_tree: &[Vec<[F; DIGEST_LEN]>],
    signer_indices: &[usize],
    pub_keys: &[XmssPublicKey],
    signatures: &[XmssSignature],
    log_inv_rate: usize,
    prox_gaps_conjecture: bool,
    overlap: usize,
) -> (Vec<F>, Vec<F>) {
    let n_sigs = signer_indices.len();
    let n_recursions = topology.children.len();
    let raw_count = topology.raw;
    let whir_config = default_whir_config(log_inv_rate, prox_gaps_conjecture);

    let bytecode_point_n_vars = bytecode.log_size() + log2_ceil_usize(N_INSTRUCTION_COLUMNS);
    let bytecode_claim_size = (bytecode_point_n_vars + 1) * DIMENSION;

    // Source 0 (raw XMSS)
    let raw_signer_indices = &signer_indices[..raw_count];
    let raw_pub_keys = &pub_keys[..raw_count];
    let raw_signatures = &signatures[..raw_count];

    // source >= 1 (recursions)
    let mut child_proofs: Vec<ChildProofData> = vec![];
    let mut child_start = raw_count;
    for (child_idx, child) in topology.children.iter().enumerate() {
        let child_count = count_signers(child, overlap);
        let child_signer_indices = &signer_indices[child_start..child_start + child_count];
        let child_pub_keys = &pub_keys[child_start..child_start + child_count];
        let child_signatures = &signatures[child_start..child_start + child_count];

        let (child_proof, inner_pub_input) = prove_aggregation_node(
            child,
            bytecode,
            message,
            slot,
            registry_merkle_tree,
            child_signer_indices,
            child_pub_keys,
            child_signatures,
            log_inv_rate,
            prox_gaps_conjecture,
            overlap,
        );

        let inner_verif_details =
            verify_execution(bytecode, &inner_pub_input, child_proof.clone(), whir_config.clone()).unwrap();

        child_proofs.push(ChildProofData {
            proof: child_proof,
            public_input: inner_pub_input,
            bytecode_evaluation: inner_verif_details.bytecode_evaluation,
        });

        child_start += child_count;
        if child_idx < topology.children.len() - 1 {
            child_start -= overlap;
        }
    }

    // Compute global signer indexes hash
    let global_indices_fe: Vec<F> = signer_indices.iter().map(|&i| F::from_usize(i)).collect();
    let signer_indexes_hash = poseidon_compress_slice(&global_indices_fe);

    //Compute per-source sub-index lists and duplicate indices
    let mut all_sub_indices = vec![raw_signer_indices.to_vec()];
    let mut dup_indices = Vec::new();
    let mut sub_start = raw_count;
    for (child_idx, child) in topology.children.iter().enumerate() {
        let child_count = count_signers(child, overlap);
        all_sub_indices.push(signer_indices[sub_start..sub_start + child_count].to_vec());
        if child_idx > 0 && overlap > 0 {
            dup_indices.extend_from_slice(&signer_indices[sub_start..sub_start + overlap]);
        }
        sub_start += child_count;
        if child_idx < topology.children.len() - 1 {
            sub_start -= overlap;
        }
    }
    dup_indices.sort();

    // Bytecode sumcheck reduction
    let (bytecode_claim_output, final_sumcheck_transcript) = if n_recursions > 0 {
        // Collect 2*n_recursions bytecode claims
        let bytecode_claim_offset = 2 + 2 * DIGEST_LEN + 2 + MESSAGE_LEN_FE + N_MERKLE_CHUNKS_FOR_SLOT;
        let mut claims = vec![];
        for child_data in &child_proofs {
            // Claim from child's public input
            let first_claim = extract_bytecode_claim_from_public_input(
                &child_data.public_input[bytecode_claim_offset..],
                bytecode_point_n_vars,
            );
            claims.push(first_claim);

            // Claim from verify_execution
            claims.push(child_data.bytecode_evaluation.clone());
        }

        let claims_hash = hash_bytecode_claims(&claims);

        let mut reduction_prover = build_prover_state();
        reduction_prover.add_base_scalars(&claims_hash);
        let alpha: EF = reduction_prover.sample();

        let n_claims = claims.len();
        let alpha_powers: Vec<EF> = alpha.powers().take(n_claims).collect();

        // Build weights: w(x) = sum_i alpha^i * eq(x, point_i)
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

        let mut ef_claim: Vec<EF> = reduced_point.0;
        ef_claim.push(reduced_value);
        let claim_output = flatten_scalars_to_base::<F, EF>(&ef_claim);
        assert_eq!(claim_output.len(), bytecode_claim_size);

        (claim_output, reduction_prover.raw_proof())
    } else {
        // n_recursions=0: output ((0,...,0), bytecode((0,...,0)))
        let mut claim_output = vec![F::ZERO; bytecode_claim_size];
        claim_output[bytecode_point_n_vars * DIMENSION] = bytecode.instructions_multilinear[0];
        (claim_output, vec![])
    };

    // Build public input
    let registry_root = &registry_merkle_tree.last().unwrap()[0];
    let non_reserved_public_input = build_non_reserved_public_input(
        n_sigs,
        n_recursions,
        registry_root,
        &signer_indexes_hash,
        message,
        slot,
        &bytecode_claim_output,
    );
    let public_memory = build_public_memory(&non_reserved_public_input);

    // header size: (n_recursions+1) pointers + 1 sumcheck_proof_ptr + 1 n_dup + n_sigs + n_dup
    let header_size = (n_recursions + 1) + 1 + 1 + n_sigs + dup_indices.len();

    let mut source_blocks: Vec<Vec<F>> = vec![];

    // Source 0: raw XMSS
    {
        let mut block = vec![];
        block.push(F::from_usize(raw_count));
        // raw_indices
        for &idx in raw_signer_indices {
            block.push(F::from_usize(idx));
        }
        // raw signer data: pubkey + registry_merkle_path + xmss_sig
        for i in 0..raw_count {
            block.extend_from_slice(&raw_pub_keys[i].merkle_root);
            let proof = get_merkle_proof(registry_merkle_tree, raw_signer_indices[i]);
            for sibling in &proof {
                block.extend_from_slice(sibling);
            }
            block.extend(encode_xmss_signature(&raw_signatures[i]));
        }
        source_blocks.push(block);
    }

    // Sources 1..n_recursions: recursive children
    for (s_idx, child_data) in child_proofs.iter().enumerate() {
        let mut block = vec![];
        let child_sub_indices = &all_sub_indices[s_idx + 1];
        let n_sub_sigs = child_sub_indices.len();

        block.push(F::from_usize(n_sub_sigs));
        // sub_indices
        for &idx in child_sub_indices {
            block.push(F::from_usize(idx));
        }
        // bytecode_value_hint (DIM elements)
        block.extend_from_slice(
            &child_data
                .bytecode_evaluation
                .value
                .as_basis_coefficients_slice()
                .to_vec(),
        );
        // inner_pub_mem
        let child_pub_mem = build_public_memory(&child_data.public_input);
        block.extend_from_slice(&child_pub_mem);
        // proof_transcript
        block.extend_from_slice(&child_data.proof);

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
    for &ptr in &source_ptrs {
        private_input.push(F::from_usize(ptr));
    }
    private_input.push(F::from_usize(bytecode_sumcheck_proof_ptr));
    private_input.push(F::from_usize(dup_indices.len()));
    for &idx in signer_indices {
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

    let time = Instant::now();
    let execution_proof = prove_execution(
        bytecode,
        (&non_reserved_public_input, &private_input),
        &vec![], // TODO precompute poseidons
        &whir_config,
        topology.profile,
    );
    let node_elapsed = time.elapsed();

    println!("{}", execution_proof.exec_summary);
    println!(
        "Node ({} sigs, {} raw, {} children, {} overlap): {:.3}s, proof {} KiB",
        n_sigs,
        raw_count,
        n_recursions,
        overlap,
        node_elapsed.as_secs_f64(),
        execution_proof.proof_size_fe * F::bits() / (8 * 1024),
    );

    (execution_proof.proof, non_reserved_public_input)
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

pub fn run_aggregation_benchmark(
    topology: &AggregationTopology,
    overlap: usize,
    log_inv_rate: usize,
    prox_gaps_conjecture: bool,
    tracing: bool,
) {
    if tracing {
        utils::init_tracing();
    }
    precompute_dft_twiddles::<F>(1 << 24);

    let n_sigs = count_signers(topology, overlap);
    let message: [F; MESSAGE_LEN_FE] = (0..MESSAGE_LEN_FE)
        .map(F::from_usize)
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();
    let slot: u32 = 1111;

    let n_unique = 10.min(n_sigs).max(1);
    let pub_keys_and_sigs: Vec<_> = (0..n_unique)
        .into_par_iter()
        .map(|i| {
            let mut rng = StdRng::seed_from_u64(i as u64);
            let start = slot - rng.random_range(0..3);
            let end = slot + rng.random_range(1..3);
            let (sk, pk) = xmss::xmss_key_gen(rng.random(), start, end).unwrap();
            let sig = xmss::xmss_sign(&mut rng, &sk, &message, slot).unwrap();
            xmss::xmss_verify(&pk, &message, &sig).unwrap();
            (pk, sig)
        })
        .collect();

    let signer_indices: Vec<usize> = (0..n_sigs).collect();
    let pub_keys: Vec<XmssPublicKey> = signer_indices
        .iter()
        .map(|&i| pub_keys_and_sigs[i % n_unique].0.clone())
        .collect();
    let signatures: Vec<XmssSignature> = signer_indices
        .iter()
        .map(|&i| pub_keys_and_sigs[i % n_unique].1.clone())
        .collect();

    // Build registry merkle tree
    let signers_for_tree: Vec<(usize, [F; DIGEST_LEN])> = signer_indices
        .iter()
        .zip(&pub_keys)
        .map(|(&idx, pk)| (idx, pk.merkle_root))
        .collect();
    let registry_layers = build_registry_merkle_tree(&signers_for_tree);

    let bytecode = compile_main_program_self_referential(prox_gaps_conjecture);
    println!("Compiled bytecode: {} instructions", bytecode.instructions.len());

    let (proof, public_input) = prove_aggregation_node(
        topology,
        &bytecode,
        &message,
        slot,
        &registry_layers,
        &signer_indices,
        &pub_keys,
        &signatures,
        log_inv_rate,
        prox_gaps_conjecture,
        overlap,
    );

    // Verify root proof
    verify_execution(
        &bytecode,
        &public_input,
        proof,
        default_whir_config(log_inv_rate, prox_gaps_conjecture),
    )
    .unwrap();
}

#[test]
fn test_recursive_aggregation() {
    let topology = AggregationTopology {
        raw: 10,
        profile: false,
        children: vec![
            AggregationTopology {
                raw: 60,
                profile: false,
                children: vec![],
            },
            AggregationTopology {
                raw: 40,
                profile: false,
                children: vec![],
            },
            AggregationTopology {
                raw: 0,
                profile: false,
                children: vec![AggregationTopology {
                    raw: 50,
                    profile: false,
                    children: vec![],
                }],
            },
        ],
    };
    run_aggregation_benchmark(&topology, 10, 2, false, false);
}
