//! Single end-to-end test vector for the Python verifier: aggregate one XMSS
//! signature using rec-aggregation, then dump the resulting bytecode, public
//! input, table metadata, and proof.
//!
//! Run:
//!     cargo test --release -p lean_prover --test dump_zkvm_vector -- --nocapture
//!
//! Output: `target/zkvm_test_vectors/proof.json` + `proof.bytecode_mle.bin`.

use std::fs;
use std::path::PathBuf;

use backend::{Air, MerkleOpening, PrimeField32};
use lean_vm::*;
use rec_aggregation::{aggregate_type_1, get_aggregation_bytecode, init_aggregation_bytecode, verify_type_1};
use serde::Serialize;
use std::io::Write;
use xmss::signers_cache::{BENCHMARK_SLOT, get_benchmark_signatures, message_for_benchmark};

type F = lean_vm::F;

const DIGEST_ELEMS: usize = 8;

fn f_to_u32(x: F) -> u32 {
    x.as_canonical_u32()
}

#[derive(Serialize)]
struct MerkleOpeningJson {
    leaf_data: Vec<u32>,
    path: Vec<[u32; DIGEST_ELEMS]>,
}

#[derive(Serialize)]
struct RawProofJson {
    /// Flat raw transcript: every absorbed group is padded to a multiple of 8
    /// (RATE) with zeros — the format the zkDSL recursion verifier reads.
    transcript: Vec<u32>,
    /// Already-restored Merkle openings (no pruning) in the order the verifier
    /// consumes them.
    merkle_openings: Vec<MerkleOpeningJson>,
}

#[derive(Serialize)]
#[serde(tag = "kind", content = "value")]
enum BusDataJson {
    Column(usize),
    Constant(usize),
}

#[derive(Serialize)]
struct BusJson {
    direction: &'static str,
    selector: usize,
    data: Vec<BusDataJson>,
}

#[derive(Serialize)]
struct LookupJson {
    index: usize,
    values: Vec<usize>,
}

#[derive(Serialize)]
struct TableInfoJson {
    name: &'static str,
    n_columns: usize,
    bus: BusJson,
    lookups: Vec<LookupJson>,
}

#[derive(Serialize)]
struct ConstantsJson {
    n_instruction_columns: usize,
    n_runtime_columns: usize,
    col_pc: usize,
    logup_memory_domainsep: usize,
    logup_precompile_domainsep: usize,
    logup_bytecode_domainsep: usize,
    max_precompile_bus_width: usize,
    starting_pc: usize,
    ending_pc: usize,
}

#[derive(Serialize)]
struct OutJson {
    /// Aggregation bytecode metadata. The multilinear is in the sidecar.
    bytecode_log_size: usize,
    bytecode_hash: [u32; DIGEST_ELEMS],
    bytecode_multilinear_path: String,
    bytecode_multilinear_len: usize,

    /// Public input to `verify_execution` (the hashed `input_data`).
    public_input: [u32; DIGEST_ELEMS],

    /// Pre-image of `public_input`. Dumped so Python can re-derive the hash.
    input_data: Vec<u32>,

    /// Per-table metadata + global constants.
    n_tables: usize,
    tables: Vec<TableInfoJson>,
    constants: ConstantsJson,
    snark_domain_sep: [u32; DIGEST_ELEMS],

    proof: RawProofJson,
}

fn convert_opening(o: &MerkleOpening<F>) -> MerkleOpeningJson {
    MerkleOpeningJson {
        leaf_data: o.leaf_data.iter().map(|&f| f_to_u32(f)).collect(),
        path: o.path.iter().map(|d| d.map(f_to_u32)).collect(),
    }
}

#[test]
fn dump_zkvm_vector() {
    let target_dir = std::env::var("CARGO_TARGET_DIR").unwrap_or_else(|_| "target".to_string());
    let out_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(&target_dir)
        .join("zkvm_test_vectors");
    fs::create_dir_all(&out_dir).unwrap();

    // Compile the aggregation program once.
    init_aggregation_bytecode();
    let bytecode = get_aggregation_bytecode();

    // Aggregate one raw XMSS signature into a TypeOneMultiSignature.
    let sig = {
        let (pk, xmss_sig) = get_benchmark_signatures()[0].clone();
        aggregate_type_1(
            &[],
            vec![(pk, xmss_sig)],
            message_for_benchmark(),
            BENCHMARK_SLOT,
            /* log_inv_rate = */ 1,
        )
        .expect("aggregate_type_1 failed")
    };

    // `verify_type_1` runs the Rust verifier (self-check) and returns the
    // restored, padded raw transcript that the zkDSL recursion verifier
    // expects — which is exactly what the Python verifier consumes.
    let verified = verify_type_1(&sig).expect("Rust verify_type_1 failed");
    let input_data = verified.input_data;
    let public_input = verified.input_data_hash;
    let raw_proof = verified.raw_proof;

    let convert_bus = |bus: Bus| BusJson {
        direction: match bus.direction {
            BusDirection::Pull => "Pull",
            BusDirection::Push => "Push",
        },
        selector: bus.selector,
        data: bus
            .data
            .into_iter()
            .map(|d| match d {
                BusData::Column(c) => BusDataJson::Column(c),
                BusData::Constant(v) => BusDataJson::Constant(v),
            })
            .collect(),
    };

    let table_infos: Vec<TableInfoJson> = ALL_TABLES
        .iter()
        .map(|t| TableInfoJson {
            name: t.name(),
            n_columns: <Table as Air>::n_columns(t),
            bus: convert_bus(t.bus()),
            lookups: t
                .lookups()
                .into_iter()
                .map(|l| LookupJson { index: l.index, values: l.values })
                .collect(),
        })
        .collect();

    // Sidecar: raw u32-LE bytecode multilinear.
    let mle_path = "proof.bytecode_mle.bin";
    {
        let mut f = fs::File::create(out_dir.join(mle_path)).unwrap();
        for v in &bytecode.instructions_multilinear {
            f.write_all(&f_to_u32(*v).to_le_bytes()).unwrap();
        }
    }

    let out = OutJson {
        bytecode_log_size: bytecode.log_size(),
        bytecode_hash: bytecode.hash.map(f_to_u32),
        bytecode_multilinear_path: mle_path.to_string(),
        bytecode_multilinear_len: bytecode.instructions_multilinear.len(),
        public_input: public_input.map(f_to_u32),
        input_data: input_data.iter().map(|&f| f_to_u32(f)).collect(),
        n_tables: N_TABLES,
        tables: table_infos,
        constants: ConstantsJson {
            n_instruction_columns: N_INSTRUCTION_COLUMNS,
            n_runtime_columns: N_RUNTIME_COLUMNS,
            col_pc: COL_PC,
            logup_memory_domainsep: LOGUP_MEMORY_DOMAINSEP,
            logup_precompile_domainsep: LOGUP_PRECOMPILE_DOMAINSEP,
            logup_bytecode_domainsep: LOGUP_BYTECODE_DOMAINSEP,
            max_precompile_bus_width: MAX_PRECOMPILE_BUS_WIDTH,
            starting_pc: STARTING_PC,
            ending_pc: ENDING_PC,
        },
        snark_domain_sep: lean_prover::SNARK_DOMAIN_SEP.map(f_to_u32),
        proof: RawProofJson {
            transcript: raw_proof.transcript.iter().map(|&f| f_to_u32(f)).collect(),
            merkle_openings: raw_proof.merkle_openings.iter().map(convert_opening).collect(),
        },
    };

    let json_path = out_dir.join("proof.json");
    fs::write(&json_path, serde_json::to_string(&out).unwrap()).unwrap();

    let mle_bytes = out_dir.join(mle_path).metadata().unwrap().len();
    println!(
        "wrote test vector:\n  {} ({:.1} KiB)\n  {} ({:.1} KiB)",
        json_path.display(),
        json_path.metadata().unwrap().len() as f64 / 1024.0,
        out_dir.join(mle_path).display(),
        mle_bytes as f64 / 1024.0,
    );
    println!(
        "  bytecode_log_size={}, transcript_len={}, input_data_len={}",
        out.bytecode_log_size,
        out.proof.transcript.len(),
        out.input_data.len(),
    );
}
