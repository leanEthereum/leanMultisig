//! Dumps a tiny zkVM proof + metadata so the Python `verify_execution`
//! port (`crates/lean_prover/verifier.py`) can run against it.
//!
//! Run:
//!     cargo test --release -p lean_prover --test dump_zkvm_vector -- --nocapture
//!
//! Output: `target/zkvm_test_vectors/small.json`. The JSON contains everything
//! Python needs to mirror `verify_execution.rs` up to (and through) any
//! sub-protocol we've ported so far.

use std::fs;
use std::path::PathBuf;

use backend::{PrimeField32, PrunedMerklePaths, WhirConfigBuilder};
use lean_compiler::*;
use lean_prover::{default_whir_config, prove_execution::prove_execution};
use lean_vm::*;
use serde::Serialize;

type F = lean_vm::F;

const DIGEST_ELEMS: usize = 8;

fn f_to_u32(x: F) -> u32 {
    x.as_canonical_u32()
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
struct BuilderJson {
    security_level: usize,
    max_num_variables_to_send_coeffs: usize,
    pow_bits: usize,
    folding_factor_first: usize,
    folding_factor_subsequent: usize,
    starting_log_inv_rate: usize,
    rs_domain_initial_reduction_factor: usize,
    soundness_type: &'static str,
}

#[derive(Serialize)]
struct TableInfoJson {
    name: &'static str,
    n_columns: usize,
}

#[derive(Serialize)]
struct OutJson {
    name: String,
    bytecode_log_size: usize,
    bytecode_hash: [u32; DIGEST_ELEMS],
    public_input: Vec<u32>,
    n_tables: usize,
    tables: Vec<TableInfoJson>,
    snark_domain_sep: [u32; DIGEST_ELEMS],
    builder: BuilderJson,
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

fn dump_one(name: &str, program_str: &str, public_input: Vec<F>, out_dir: &PathBuf) {
    let bytecode = compile_program(&ProgramSource::Raw(program_str.to_string()));
    let starting_log_inv_rate = 1;
    let builder: WhirConfigBuilder = default_whir_config(starting_log_inv_rate);
    let witness = ExecutionWitness::default();
    let exec_proof = prove_execution(&bytecode, &public_input, &witness, &builder, false)
        .expect("prove_execution failed");

    let table_infos: Vec<TableInfoJson> = ALL_TABLES
        .iter()
        .map(|t| TableInfoJson {
            name: t.name(),
            n_columns: <Table as backend::Air>::n_columns(t),
        })
        .collect();

    let out = OutJson {
        name: name.to_string(),
        bytecode_log_size: bytecode.log_size(),
        bytecode_hash: bytecode.hash.map(f_to_u32),
        public_input: public_input.iter().map(|&f| f_to_u32(f)).collect(),
        n_tables: N_TABLES,
        tables: table_infos,
        snark_domain_sep: lean_prover::SNARK_DOMAIN_SEP.map(f_to_u32),
        builder: BuilderJson {
            security_level: 124,
            max_num_variables_to_send_coeffs: 8,
            pow_bits: 16,
            folding_factor_first: 7,
            folding_factor_subsequent: 5,
            starting_log_inv_rate,
            rs_domain_initial_reduction_factor: 5,
            soundness_type: "JohnsonBound",
        },
        proof: ProofJson {
            transcript: exec_proof.proof.transcript.iter().map(|&f| f_to_u32(f)).collect(),
            merkle_paths: exec_proof.proof.merkle_paths.iter().map(convert_pruned).collect(),
        },
    };

    let path = out_dir.join(format!("{name}.json"));
    fs::write(&path, serde_json::to_string(&out).unwrap()).unwrap();
    println!(
        "{} -> {} ({:.1} KiB; bytecode_log_size={}, transcript_len={})",
        name,
        path.display(),
        path.metadata().unwrap().len() as f64 / 1024.0,
        out.bytecode_log_size,
        out.proof.transcript.len(),
    );
}

#[test]
fn dump_zkvm_vector() {
    let target_dir = std::env::var("CARGO_TARGET_DIR").unwrap_or_else(|_| "target".to_string());
    let out_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(&target_dir)
        .join("zkvm_test_vectors");
    fs::create_dir_all(&out_dir).unwrap();

    // The smallest legal program. Empty public input.
    let small_program = r#"
def main():
    a = Array(1)
    for i in unroll(0, 2**17):
        a[0] = 1 * 2
    return
"#;
    dump_one("small", small_program, vec![], &out_dir);
}
