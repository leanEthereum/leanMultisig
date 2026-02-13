use lean_prover::default_whir_config;
use lean_prover::verify_execution::verify_execution;
use lean_vm::*;
use multilinear_toolkit::prelude::*;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use xmss::{MESSAGE_LEN_FE, XmssPublicKey, XmssSignature};

use crate::compilation::compile_main_program_self_referential;
use crate::{AggregatedSigs, AggregationTopology, build_registry_merkle_tree, count_signers, aggregate_merge};

#[allow(clippy::too_many_arguments)]
fn build_aggregation(
    topology: &AggregationTopology,
    bytecode: &Bytecode,
    message: &[F; MESSAGE_LEN_FE],
    slot: u32,
    registry_merkle_tree: &[Vec<[F; DIGEST_LEN]>],
    signer_indices: &[usize],
    pub_keys: &[XmssPublicKey],
    signatures: &[XmssSignature],
    overlap: usize,
    log_inv_rate: usize,
    prox_gaps_conjecture: bool,
) -> AggregatedSigs {
    let raw_count = topology.raw_xmss;
    let raw_signers: Vec<(usize, XmssPublicKey, XmssSignature)> = (0..raw_count)
        .map(|i| (signer_indices[i], pub_keys[i].clone(), signatures[i].clone()))
        .collect();

    let mut child_results = vec![];
    let mut child_start = raw_count;
    for (child_idx, child) in topology.children.iter().enumerate() {
        let child_count = count_signers(child, overlap);
        let child_agg = build_aggregation(
            child,
            bytecode,
            message,
            slot,
            registry_merkle_tree,
            &signer_indices[child_start..child_start + child_count],
            &pub_keys[child_start..child_start + child_count],
            &signatures[child_start..child_start + child_count],
            overlap,
            log_inv_rate,
            prox_gaps_conjecture,
        );
        child_results.push(child_agg);
        child_start += child_count;
        if child_idx < topology.children.len() - 1 {
            child_start -= overlap;
        }
    }

    aggregate_merge(
        &child_results,
        &raw_signers,
        message,
        slot,
        registry_merkle_tree,
        bytecode,
        overlap,
        log_inv_rate,
        prox_gaps_conjecture,
    )
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

    let result = build_aggregation(
        topology,
        &bytecode,
        &message,
        slot,
        &registry_layers,
        &signer_indices,
        &pub_keys,
        &signatures,
        overlap,
        log_inv_rate,
        prox_gaps_conjecture,
    );

    // Verify root proof
    let registry_root = &registry_layers.last().unwrap()[0];
    let public_input = result.public_input(registry_root, &message, slot, &bytecode);
    verify_execution(
        &bytecode,
        &public_input,
        result.proof,
        default_whir_config(log_inv_rate, prox_gaps_conjecture),
    )
    .unwrap();
}

#[test]
fn test_recursive_aggregation() {
    let topology = AggregationTopology {
        raw_xmss: 10,
        children: vec![
            AggregationTopology {
                raw_xmss: 60,
                children: vec![],
            },
            AggregationTopology {
                raw_xmss: 40,
                children: vec![],
            },
            AggregationTopology {
                raw_xmss: 0,
                children: vec![AggregationTopology {
                    raw_xmss: 50,
                    children: vec![],
                }],
            },
        ],
    };
    run_aggregation_benchmark(&topology, 10, 2, false, false);
}
