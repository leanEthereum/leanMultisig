mod cache;

use std::collections::{BTreeMap, HashMap};
use std::time::Instant;

use backend::{Algebra, BasedVectorSpace, PrimeCharacteristicRing, Proof, TwoAdicField};
use clap::Parser;
use lean_compiler::{CompilationFlags, ProgramSource, compile_program_with_flags};
use lean_prover::{
    default_whir_config,
    prove_execution::{ExecutionProof, prove_execution},
    verify_execution::verify_execution,
};
use lean_vm::{Bytecode, EF, ExecutionWitness, F};
use rand::{RngExt, SeedableRng, rngs::StdRng};

static EMBEDDED_ZK_DSL: include_dir::Dir<'_> = include_dir::include_dir!("$CARGO_MANIFEST_DIR/zkdsl_implem");

const STARTING_LOG_INV_RATE: usize = 1;

pub const LOG_M: usize = 13; // Blob ≈ 155 KiB = 2^13 extension field elements (= 2^13 * 5 base field elements)
pub const DEFAULT_N_BLOBS: usize = 8;

#[derive(Parser)]
#[command(about = "Reed-Solomon DA: hash N_BLOBS codewords, run a random parity check, then prove + verify")]
struct Cli {
    #[arg(long, help = "Number of blobs to commit", default_value_t = DEFAULT_N_BLOBS)]
    n_blobs: usize,
    #[arg(long, help = "Enable tracing")]
    tracing: bool,
}

fn main() {
    // cargo run --release -p lean-da -- --n-blobs 34
    let cli = Cli::parse();
    if cli.tracing {
        utils::init_tracing();
    }

    let bytecode = compile_lean_da_bytecode(cli.n_blobs);
    let public_input: Vec<F> = vec![];
    let proof = prove_lean_da(&bytecode, &public_input, cli.n_blobs);
    verify_lean_da(&bytecode, &public_input, proof.proof);
}

pub fn compile_lean_da_bytecode(n_blobs: usize) -> Bytecode {
    let mut replacements = BTreeMap::new();
    replacements.insert("LOG_M_PLACEHOLDER".to_string(), LOG_M.to_string());
    replacements.insert("N_BLOBS_PLACEHOLDER".to_string(), n_blobs.to_string());

    if let Some((bytecode, _)) = cache::try_load(&EMBEDDED_ZK_DSL, &replacements) {
        println!("(Compilation cache hit)");
        return bytecode;
    }

    let time = Instant::now();
    let source = ProgramSource::Embedded {
        entry: "lean_da.py".to_string(),
        dir: &EMBEDDED_ZK_DSL,
    };
    let bytecode = compile_program_with_flags(
        &source,
        CompilationFlags {
            replacements: replacements.clone(),
        },
    );
    println!("Compilation time: {:.3} s", time.elapsed().as_secs_f64());

    if let Err(e) = cache::try_store(&EMBEDDED_ZK_DSL, &replacements, &bytecode) {
        eprintln!("Warning: failed to write bytecode cache: {e}");
    }

    bytecode
}

fn ntt<A: Algebra<F> + Copy>(a: &mut [A]) {
    let n = a.len();
    assert!(n.is_power_of_two());
    let log_n = n.trailing_zeros() as usize;

    let shift = usize::BITS as usize - log_n;
    for i in 0..n {
        let j = i.reverse_bits() >> shift;
        if i < j {
            a.swap(i, j);
        }
    }

    let mut size = 2;
    while size <= n {
        let half = size / 2;
        let root = F::two_adic_generator(size.trailing_zeros() as usize);
        for chunk_start in (0..n).step_by(size) {
            let mut twiddle = F::ONE;
            for i in 0..half {
                let u = a[chunk_start + i];
                let v = a[chunk_start + i + half] * twiddle;
                a[chunk_start + i] = u + v;
                a[chunk_start + i + half] = u - v;
                twiddle *= root;
            }
        }
        size *= 2;
    }
}

fn rs_encode<A: Algebra<F> + Copy>(message: &[A]) -> Vec<A> {
    let m = message.len();
    assert!(m.is_power_of_two());
    let mut codeword = vec![A::ZERO; 2 * m];
    codeword[..m].copy_from_slice(message);
    ntt(&mut codeword);
    codeword
}

fn build_witness(n_blobs: usize) -> ExecutionWitness {
    let m = 1 << LOG_M;
    let dim = <EF as BasedVectorSpace<F>>::DIMENSION;
    let mut rng = StdRng::seed_from_u64(0);
    let mut codewords: Vec<F> = Vec::with_capacity(n_blobs * 2 * m * dim);
    for _ in 0..n_blobs {
        let message: Vec<EF> = (0..m).map(|_| rng.random()).collect();
        let codeword = rs_encode(&message);
        for j in 0..m {
            codewords.extend_from_slice(<EF as BasedVectorSpace<F>>::as_basis_coefficients_slice(
                &codeword[2 * j],
            ));
        }
        for j in 0..m {
            codewords.extend_from_slice(<EF as BasedVectorSpace<F>>::as_basis_coefficients_slice(
                &codeword[2 * j + 1],
            ));
        }
    }

    let mut hints: HashMap<String, Vec<Vec<F>>> = HashMap::new();
    hints.insert("codewords".to_string(), vec![codewords]);
    ExecutionWitness {
        preamble_memory_len: 0,
        hints,
    }
}

pub fn prove_lean_da(bytecode: &Bytecode, public_input: &[F], n_blobs: usize) -> ExecutionProof {
    const F_BITS: usize = 31;

    let witness = build_witness(n_blobs);
    let t0 = Instant::now();
    let proof = prove_execution(
        bytecode,
        public_input,
        &witness,
        &default_whir_config(STARTING_LOG_INV_RATE),
        false,
    )
    .unwrap();
    let proving_time = t0.elapsed();

    let meta = proof.metadata.as_ref().expect("metadata missing");
    let proof_size_fe = proof.proof.proof_size_fe();
    let proof_kib = (proof_size_fe * F_BITS) as f64 / (8.0 * 1024.0);
    // Each blob is 2^LOG_M extension elements, i.e. 2^LOG_M * DIM base field elements.
    let blob_size_fe = (1 << LOG_M) * <EF as BasedVectorSpace<F>>::DIMENSION;
    let total_data_kib = (n_blobs * blob_size_fe * F_BITS) as f64 / (8.0 * 1024.0);
    let throughput_kib_per_s = total_data_kib / proving_time.as_secs_f64();
    println!("Bytecode size:    {}", meta.bytecode_size);
    println!("Cycles:           {}", meta.cycles);
    println!("Poseidon16 calls: {}", meta.n_poseidons);
    println!("ExtensionOp calls:{}", meta.n_extension_ops);
    println!("Proving time:     {:.3} s", proving_time.as_secs_f64());
    println!("Proof size:       {:.2} KiB", proof_kib);
    println!(
        "Throughput:       {:.2} KiB/s ({} blobs * {} FE / {:.3} s)",
        throughput_kib_per_s,
        n_blobs,
        blob_size_fe,
        proving_time.as_secs_f64()
    );

    proof
}

pub fn verify_lean_da(bytecode: &Bytecode, public_input: &[F], proof: Proof<F>) {
    verify_execution(bytecode, public_input, proof).unwrap();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_compile_prove_verify() {
        // cargo test --release --package lean-da -- tests::test_compile_prove_verify --nocapture
        let bytecode = compile_lean_da_bytecode(DEFAULT_N_BLOBS);
        let public_input: Vec<F> = vec![];
        let proof = prove_lean_da(&bytecode, &public_input, DEFAULT_N_BLOBS);
        verify_lean_da(&bytecode, &public_input, proof.proof);
    }

    #[test]
    fn test_rs_encode_matches_naive() {
        let mut rng = StdRng::seed_from_u64(7);
        let m: usize = 1 << LOG_M;
        let message: Vec<EF> = (0..m).map(|_| rng.random()).collect();
        let two_m = 2 * m;
        let w = F::two_adic_generator(two_m.trailing_zeros() as usize);
        let naive: Vec<EF> = (0..two_m)
            .map(|j| {
                let wj = w.exp_u64(j as u64);
                message.iter().rev().fold(EF::ZERO, |acc, &c| acc * wj + c)
            })
            .collect();
        assert_eq!(rs_encode(&message), naive);
    }
}
