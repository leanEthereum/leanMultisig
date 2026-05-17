//! Generates WHIR test vectors for the Python verifier.
//!
//! Run:
//!     cargo test --release -p mt-whir --test dump_test_vectors -- --nocapture
//!
//! Outputs `target/whir_test_vectors/<name>.json`. Each file contains, in
//! canonical (non-Monty) `u32` form:
//!
//!   - `num_variables`, `log_inv_rate`, WHIR builder params,
//!   - `statement`: list of `SparseStatement` (point + values),
//!   - `proof.transcript`: the raw `Vec<F>` written by the prover,
//!   - `proof.merkle_paths`: pruned Merkle paths exactly as serialized by
//!     `PrunedMerklePaths` (Python must port the restore routine),
//!   - `expected_folding_randomness`: what `WhirConfig::verify` returns.

use std::fs;
use std::path::PathBuf;

use fiat_shamir::{ProverState, VerifierState};
use field::{PrimeCharacteristicRing, PrimeField32, TwoAdicField};
use koala_bear::{KoalaBear, QuinticExtensionFieldKB, default_koalabear_poseidon1_16};
use mt_whir::*;
use poly::*;
use rand::{RngExt, SeedableRng, rngs::StdRng};
use serde::Serialize;

type F = KoalaBear;
type EF = QuinticExtensionFieldKB;

const DIGEST_ELEMS: usize = 8;

fn f_to_u32(x: F) -> u32 {
    x.as_canonical_u32()
}

fn ef_to_u32s(x: EF) -> [u32; 5] {
    use field::BasedVectorSpace;
    let coeffs: &[F] = x.as_basis_coefficients_slice();
    [
        f_to_u32(coeffs[0]),
        f_to_u32(coeffs[1]),
        f_to_u32(coeffs[2]),
        f_to_u32(coeffs[3]),
        f_to_u32(coeffs[4]),
    ]
}

#[derive(Serialize)]
struct SparseValueJson {
    selector: usize,
    value: [u32; 5],
}

#[derive(Serialize)]
struct SparseStatementJson {
    total_num_variables: usize,
    is_next: bool,
    point: Vec<[u32; 5]>,
    values: Vec<SparseValueJson>,
}

#[derive(Serialize)]
struct PrunedPathJson {
    leaf_index: usize,
    siblings: Vec<[u32; DIGEST_ELEMS]>,
}

#[derive(Serialize)]
struct PrunedMerklePathsJson {
    merkle_height: usize,
    original_order: Vec<usize>,
    leaf_data: Vec<Vec<u32>>,
    paths: Vec<PrunedPathJson>,
    n_trailing_zeros: usize,
}

#[derive(Serialize)]
struct ProofJson {
    transcript: Vec<u32>,
    merkle_paths: Vec<PrunedMerklePathsJson>,
}

#[derive(Serialize)]
struct WhirBuilderJson {
    security_level: usize,
    max_num_variables_to_send_coeffs: usize,
    pow_bits: usize,
    folding_factor_first: usize,
    folding_factor_subsequent: usize,
    starting_log_inv_rate: usize,
    rs_domain_initial_reduction_factor: usize,
    soundness_type: &'static str, // "JohnsonBound"
}

#[derive(Serialize)]
struct TestVectorJson {
    name: String,
    num_variables: usize,
    log_inv_rate: usize,
    builder: WhirBuilderJson,
    statement: Vec<SparseStatementJson>,
    proof: ProofJson,
    expected_folding_randomness: Vec<[u32; 5]>,
}

fn convert_pruned(p: &fiat_shamir::PrunedMerklePaths<F, F>) -> PrunedMerklePathsJson {
    PrunedMerklePathsJson {
        merkle_height: p.merkle_height,
        original_order: p.original_order.clone(),
        leaf_data: p
            .leaf_data
            .iter()
            .map(|v| v.iter().map(|&f| f_to_u32(f)).collect())
            .collect(),
        paths: p
            .paths
            .iter()
            .map(|(idx, siblings)| PrunedPathJson {
                leaf_index: *idx,
                siblings: siblings.iter().map(|d| d.map(f_to_u32)).collect(),
            })
            .collect(),
        n_trailing_zeros: p.n_trailing_zeros,
    }
}

fn convert_statement(s: &SparseStatement<EF>) -> SparseStatementJson {
    SparseStatementJson {
        total_num_variables: s.total_num_variables,
        is_next: s.is_next,
        point: s.point.iter().map(|&p| ef_to_u32s(p)).collect(),
        values: s
            .values
            .iter()
            .map(|v| SparseValueJson {
                selector: v.selector,
                value: ef_to_u32s(v.value),
            })
            .collect(),
    }
}

fn run_one(name: &str, num_variables: usize, log_inv_rate: usize, seed: u64, out_dir: &PathBuf) {
    let poseidon16 = default_koalabear_poseidon1_16();

    // Use the same defaults as `lean_prover::default_whir_config`, so the
    // Python side can reuse the dumped WhirConfig table.
    let builder = WhirConfigBuilder {
        security_level: 124,
        max_num_variables_to_send_coeffs: 8,
        pow_bits: 16,
        folding_factor: FoldingFactor::new(7, 5),
        soundness_type: SecurityAssumption::JohnsonBound,
        starting_log_inv_rate: log_inv_rate,
        rs_domain_initial_reduction_factor: 5,
    };
    let params = WhirConfig::<EF>::new(&builder, num_variables);

    let mut rng = StdRng::seed_from_u64(seed);
    let num_coeffs = 1usize << num_variables;
    let polynomial: Vec<F> = (0..num_coeffs).map(|_| rng.random::<F>()).collect();

    // One simple statement: a fully-dense point + its evaluation.
    let dense_point: Vec<EF> = (0..num_variables).map(|_| rng.random()).collect();
    let dense_value = polynomial.evaluate_sparse(0, &MultilinearPoint(dense_point.clone()));
    let statement = vec![SparseStatement::new(
        num_variables,
        MultilinearPoint(dense_point.clone()),
        vec![SparseValue {
            selector: 0,
            value: dense_value,
        }],
    )];

    precompute_dft_twiddles::<F>(1 << F::TWO_ADICITY);

    let mut prover_state = ProverState::<EF, _>::new(poseidon16.clone());
    let polynomial_mle: MleOwned<EF> = MleOwned::Base(polynomial);
    let witness = params.commit(&mut prover_state, &polynomial_mle, num_coeffs);
    params.prove(&mut prover_state, statement.clone(), witness, &polynomial_mle.by_ref());
    let proof = prover_state.into_proof();

    // Run the verifier and capture its `folding_randomness` output as the oracle.
    let mut vstate = VerifierState::<EF, _>::new(proof.clone(), poseidon16.clone()).unwrap();
    println!("transcript[23] (pre-verify): {}", proof.transcript[23].as_canonical_u32());
    let parsed_commitment = params.parse_commitment::<F>(&mut vstate).unwrap();
    let folding_randomness = params
        .verify::<F>(&mut vstate, &parsed_commitment, statement.clone())
        .unwrap();

    let entry = TestVectorJson {
        name: name.to_string(),
        num_variables,
        log_inv_rate,
        builder: WhirBuilderJson {
            security_level: 124,
            max_num_variables_to_send_coeffs: 8,
            pow_bits: 16,
            folding_factor_first: 7,
            folding_factor_subsequent: 5,
            starting_log_inv_rate: log_inv_rate,
            rs_domain_initial_reduction_factor: 5,
            soundness_type: "JohnsonBound",
        },
        statement: statement.iter().map(convert_statement).collect(),
        proof: ProofJson {
            transcript: proof.transcript.iter().map(|&f| f_to_u32(f)).collect(),
            merkle_paths: proof.merkle_paths.iter().map(convert_pruned).collect(),
        },
        expected_folding_randomness: folding_randomness.iter().map(|&p| ef_to_u32s(p)).collect(),
    };

    let path = out_dir.join(format!("{name}.json"));
    let json = serde_json::to_string(&entry).unwrap();
    fs::write(&path, json).unwrap_or_else(|e| panic!("write {}: {e}", path.display()));
    println!(
        "  {} -> {} ({:.1} KiB)",
        name,
        path.display(),
        path.metadata().unwrap().len() as f64 / 1024.0,
    );
}

/// Tiny sanity test for the Python Merkle restoration. Build a 16-leaf tree,
/// open a handful of indices, prune, then dump (a) the original openings (as
/// the source of truth) and (b) the pruned form Python should restore.
#[test]
fn dump_merkle_vector() {
    use fiat_shamir::{MerklePath, MerklePaths, PrunedMerklePaths};
    use symetric::compress;

    let poseidon = default_koalabear_poseidon1_16();

    // Build 16 leaves, each 8 base elements long (one RATE block).
    let n = 16usize;
    let leaf_len = 8usize;
    let leaves: Vec<Vec<F>> = (0..n)
        .map(|i| {
            (0..leaf_len)
                .map(|j| F::from_u32((i * 100 + j) as u32 + 1))
                .collect()
        })
        .collect();

    // Hash each leaf to get level 0.
    let hash_leaf = |data: &[F]| {
        // The two-RATE-blocks requirement of hash_slice needs len(data) >= 16
        // (i.e. n_chunks >= 2). For an 8-element leaf, pad with one extra zero
        // block so n_chunks = 2.
        let mut padded = vec![F::ZERO; 8];
        padded.extend_from_slice(data);
        symetric::hash_slice::<_, _, 16, 8, 8>(&poseidon, &padded)
    };
    let hash_combine =
        |l: &[F; 8], r: &[F; 8]| compress::<_, _, 8, 16>(&poseidon, [*l, *r]);

    let leaf_hashes: Vec<[F; 8]> = leaves.iter().map(|l| hash_leaf(l)).collect();
    let mut levels = vec![leaf_hashes];
    let mut log_h = n.trailing_zeros() as usize;
    while levels.last().unwrap().len() > 1 {
        let prev = levels.last().unwrap();
        let next: Vec<[F; 8]> = (0..prev.len() / 2)
            .map(|i| hash_combine(&prev[2 * i], &prev[2 * i + 1]))
            .collect();
        levels.push(next);
    }
    let _ = log_h;
    let root: [F; 8] = *levels.last().unwrap().first().unwrap();

    let make_path = |idx: usize| -> MerklePath<F, F> {
        let mut sibling_hashes = Vec::with_capacity(levels.len() - 1);
        let mut k = idx;
        for level in &levels[..levels.len() - 1] {
            sibling_hashes.push(level[k ^ 1]);
            k >>= 1;
        }
        // Pad leaf data with the zero-block prefix used by hash_leaf.
        let mut leaf_padded = vec![F::ZERO; 8];
        leaf_padded.extend_from_slice(&leaves[idx]);
        MerklePath {
            leaf_data: leaf_padded,
            sibling_hashes,
            leaf_index: idx,
        }
    };

    let indices = vec![3usize, 7, 11, 0, 11]; // duplicate included
    let original = MerklePaths(indices.iter().map(|&i| make_path(i)).collect::<Vec<_>>());
    let pruned: PrunedMerklePaths<F, F> = original.clone().prune();

    #[derive(serde::Serialize)]
    struct PathJson {
        leaf_index: usize,
        leaf_data: Vec<u32>,
        sibling_hashes: Vec<[u32; 8]>,
    }

    #[derive(serde::Serialize)]
    struct Out {
        root: [u32; 8],
        original: Vec<PathJson>,
        pruned: PrunedMerklePathsJson,
    }

    let out = Out {
        root: root.map(f_to_u32),
        original: original
            .clone()
            .0
            .into_iter()
            .map(|p| PathJson {
                leaf_index: p.leaf_index,
                leaf_data: p.leaf_data.iter().map(|&f| f_to_u32(f)).collect(),
                sibling_hashes: p.sibling_hashes.iter().map(|d| d.map(f_to_u32)).collect(),
            })
            .collect(),
        pruned: convert_pruned(&pruned),
    };

    let target_dir = std::env::var("CARGO_TARGET_DIR").unwrap_or_else(|_| "target".to_string());
    let out_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(&target_dir)
        .join("whir_test_vectors");
    fs::create_dir_all(&out_dir).unwrap();
    let path = out_dir.join("merkle_sanity.json");
    fs::write(&path, serde_json::to_string_pretty(&out).unwrap()).unwrap();
    println!("wrote merkle sanity to {}", path.display());
}

/// Cross-check that Python's Poseidon16 permutation matches Rust's on a
/// specific input.
#[test]
fn dump_permute_oracle() {
    use koala_bear::symmetric::Permutation;
    let poseidon = default_koalabear_poseidon1_16();

    // Input: the state captured after_read_poly0, with rate replaced by
    // [witness, 0, ..., 0] (witness = 66589315).
    let input: [F; 16] = [
        1732812002, 1231764113, 2063040591, 339182820,
        1169456582, 2099684484, 1027478197, 686152220,
        66589315, 0, 0, 0, 0, 0, 0, 0,
    ].map(F::from_u32);
    let mut state = input;
    poseidon.permute_mut(&mut state);

    #[derive(serde::Serialize)]
    struct Out {
        input: Vec<u32>,
        output: Vec<u32>,
    }
    let out = Out {
        input: input.iter().map(|&f| f_to_u32(f)).collect(),
        output: state.iter().map(|&f| f_to_u32(f)).collect(),
    };
    let target_dir = std::env::var("CARGO_TARGET_DIR").unwrap_or_else(|_| "target".to_string());
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(&target_dir)
        .join("whir_test_vectors")
        .join("permute_oracle.json");
    fs::write(&path, serde_json::to_string_pretty(&out).unwrap()).unwrap();
    println!("output: {:?}", out.output);
}

#[test]
fn dump_test_vectors() {
    let target_dir =
        std::env::var("CARGO_TARGET_DIR").unwrap_or_else(|_| "target".to_string());
    let out_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(&target_dir)
        .join("whir_test_vectors");
    fs::create_dir_all(&out_dir).unwrap();

    println!("Writing test vectors to {}", out_dir.display());

    // `n_rounds` is 0 below `num_variables = 16` with the default builder, and
    // `final_round_config()` would then panic. Keep all entries above that.
    run_one("small_lir1_nv16", 16, 1, 0xdead_beef, &out_dir);
    run_one("small_lir2_nv18", 18, 2, 0xfeed_face, &out_dir);
    run_one("medium_lir1_nv20", 20, 1, 0xcafe_babe, &out_dir);
}
