//! Focused test vector for the GKR-quotient sub-protocol. Independent of the
//! rest of the zkVM verifier so the Python port can be validated in isolation.
//!
//! Run:
//!     cargo test --release -p lean_prover --test dump_gkr_vector -- --nocapture

use std::fs;
use std::path::PathBuf;

use backend::{
    BasedVectorSpace, Field, MleOwned, PackedValue, PrimeCharacteristicRing, PrimeField32,
    ProverState, PrunedMerklePaths, VerifierState, default_koalabear_poseidon1_16, pack_extension,
    packing_log_width,
};
use lean_vm::{EF, F};
use rand::{RngExt, SeedableRng, rngs::StdRng};
use serde::Serialize;
use sub_protocols::{ENDIANNESS_PIVOT_GKR, prove_gkr_quotient, verify_gkr_quotient};

const DIGEST_ELEMS: usize = 8;

fn f_to_u32(x: F) -> u32 {
    x.as_canonical_u32()
}

fn ef_to_u32s(x: EF) -> [u32; 5] {
    let coords: &[F] = x.as_basis_coefficients_slice();
    [
        f_to_u32(coords[0]),
        f_to_u32(coords[1]),
        f_to_u32(coords[2]),
        f_to_u32(coords[3]),
        f_to_u32(coords[4]),
    ]
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
struct GkrOut {
    name: String,
    n_vars: usize,
    expected_quotient: [u32; 5],
    expected_point: Vec<[u32; 5]>,
    expected_claims_num: [u32; 5],
    expected_claims_den: [u32; 5],
    proof: ProofJson,
}

fn convert_pruned(p: &PrunedMerklePaths<F, F>) -> PrunedMerklePathsJson {
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

/// Copy of the helper used in the existing GKR test (bit-reverse the input
/// chunks at `chunk_log`).
fn bit_reverse_chunks<T: Copy>(v: &[T], chunk_log: usize) -> Vec<T> {
    let chunk = 1 << chunk_log;
    let shift = (usize::BITS as usize) - chunk_log;
    let mut out = Vec::with_capacity(v.len());
    for chunk_start in (0..v.len()).step_by(chunk) {
        for i in 0..chunk {
            out.push(v[chunk_start + (i.reverse_bits() >> shift)]);
        }
    }
    out
}

fn run_one(name: &str, log_n: usize, seed: u64, out_dir: &PathBuf) {
    let poseidon16 = default_koalabear_poseidon1_16();
    let pivot = ENDIANNESS_PIVOT_GKR.min(log_n);
    let n = 1usize << log_n;

    let mut rng = StdRng::seed_from_u64(seed);
    let c: EF = rng.random();
    let numerators_raw: Vec<F> = (0..n).map(|_| rng.random()).collect();
    let denominators_raw: Vec<EF> = (0..n).map(|_| c - F::from_usize(rng.random_range(..n))).collect();

    // Bit-reverse + pack the inputs at `pivot` (prover convention).
    let w = packing_log_width::<EF>();
    let nums_br = {
        let mut br = vec![F::ZERO; n];
        let chunk = 1 << pivot;
        let shift = (usize::BITS as usize) - pivot;
        for c_start in (0..n).step_by(chunk) {
            for i in 0..chunk {
                br[c_start + i] = numerators_raw[c_start + (i.reverse_bits() >> shift)];
            }
        }
        use backend::PFPacking;
        let packed: Vec<PFPacking<EF>> = PFPacking::<EF>::pack_slice(&br).to_vec();
        packed
    };
    let dens_br: Vec<backend::EFPacking<EF>> = pack_extension(&bit_reverse_chunks(&denominators_raw, pivot));
    let _ = w;

    let mut prover_state = ProverState::<EF, _>::new(poseidon16.clone());
    let (quotient_prover, claim_point_prover) =
        prove_gkr_quotient::<EF>(&mut prover_state, &nums_br, &dens_br, pivot);
    let proof = prover_state.into_proof();

    let mut verifier_state = VerifierState::<EF, _>::new(proof.clone(), poseidon16).unwrap();
    let (retrieved_quotient, claim_point, claim_num, claim_den) =
        verify_gkr_quotient::<EF>(&mut verifier_state, log_n).unwrap();
    assert_eq!(quotient_prover, retrieved_quotient);
    assert_eq!(claim_point_prover, claim_point);

    // sanity: evaluate the raw inputs at claim_point and check they match.
    let nums_nat = MleOwned::<EF>::Base(numerators_raw.clone());
    let dens_nat = MleOwned::<EF>::Extension(denominators_raw.clone());
    assert_eq!(nums_nat.evaluate(&claim_point), claim_num);
    assert_eq!(dens_nat.evaluate(&claim_point), claim_den);

    let out = GkrOut {
        name: name.to_string(),
        n_vars: log_n,
        expected_quotient: ef_to_u32s(retrieved_quotient),
        expected_point: claim_point.0.iter().map(|&p| ef_to_u32s(p)).collect(),
        expected_claims_num: ef_to_u32s(claim_num),
        expected_claims_den: ef_to_u32s(claim_den),
        proof: ProofJson {
            transcript: proof.transcript.iter().map(|&f| f_to_u32(f)).collect(),
            merkle_paths: proof.merkle_paths.iter().map(convert_pruned).collect(),
        },
    };

    let path = out_dir.join(format!("{name}.json"));
    fs::write(&path, serde_json::to_string(&out).unwrap()).unwrap();
    println!(
        "{} -> {} ({:.1} KiB) [n_vars={}, transcript_len={}]",
        name,
        path.display(),
        path.metadata().unwrap().len() as f64 / 1024.0,
        log_n,
        out.proof.transcript.len(),
    );
}

#[test]
fn dump_gkr_vector() {
    let target_dir = std::env::var("CARGO_TARGET_DIR").unwrap_or_else(|_| "target".to_string());
    let out_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(&target_dir)
        .join("gkr_test_vectors");
    fs::create_dir_all(&out_dir).unwrap();

    // n_vars must exceed N_VARS_TO_SEND_GKR_COEFFS=5, and `prove_gkr_quotient`
    // requires `pivot > w` (w = packing_log_width). pivot is capped at
    // ENDIANNESS_PIVOT_GKR = 12, but for small inputs it shrinks to log_n —
    // make sure to stay above the packing width.
    run_one("small_nv13", 13, 0xdead_beef, &out_dir);
}
