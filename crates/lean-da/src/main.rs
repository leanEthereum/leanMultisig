mod cache;

use std::collections::{BTreeMap, HashMap};
use std::time::Instant;

use backend::{Algebra, BasedVectorSpace, Field, PrimeCharacteristicRing, Proof, TwoAdicField};
use clap::{Parser, ValueEnum};
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
    #[arg(long, value_enum, default_value_t = Construction::Baseline, help = "leanDA construction to run")]
    construction: Construction,
    #[arg(long, help = "Enable tracing")]
    tracing: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, ValueEnum)]
pub enum Construction {
    Baseline,
    OodRow,
    OodRowColumnMajor,
    OodRowTiled,
}

impl Construction {
    fn entry(self) -> &'static str {
        match self {
            Self::Baseline => "lean_da.py",
            Self::OodRow => "lean_da_ood.py",
            Self::OodRowColumnMajor => "lean_da_ood_column_major.py",
            Self::OodRowTiled => "lean_da_ood_tiled.py",
        }
    }

    fn label(self) -> &'static str {
        match self {
            Self::Baseline => "baseline",
            Self::OodRow => "ood-row",
            Self::OodRowColumnMajor => "ood-row-column-major",
            Self::OodRowTiled => "ood-row-tiled",
        }
    }
}

fn main() {
    // cargo run --release -p lean-da -- --n-blobs 48
    let cli = Cli::parse();
    if cli.tracing {
        utils::init_tracing();
    }

    let bytecode = compile_lean_da_bytecode(cli.n_blobs, cli.construction);
    let (witness, public_input) = build_instance(cli.n_blobs, cli.construction);
    let proof = prove_lean_da(&bytecode, &public_input, &witness, cli.n_blobs, cli.construction);
    verify_lean_da(&bytecode, &public_input, proof.proof);
}

pub fn compile_lean_da_bytecode(n_blobs: usize, construction: Construction) -> Bytecode {
    assert!(n_blobs > 0, "n_blobs must be nonzero");
    if matches!(
        construction,
        Construction::OodRow | Construction::OodRowColumnMajor | Construction::OodRowTiled
    ) {
        assert!(
            n_blobs.is_power_of_two(),
            "ood-row constructions require n_blobs to be a power of two"
        );
    }

    let mut replacements = BTreeMap::new();
    replacements.insert("LEAN_DA_ENTRY".to_string(), construction.entry().to_string());
    replacements.insert("LOG_M_PLACEHOLDER".to_string(), LOG_M.to_string());
    replacements.insert("N_BLOBS_PLACEHOLDER".to_string(), n_blobs.to_string());
    replacements.insert(
        "LOG_N_BLOBS_PLACEHOLDER".to_string(),
        if n_blobs.is_power_of_two() {
            log2_exact_power_of_two(n_blobs).to_string()
        } else {
            "0".to_string()
        },
    );

    if let Some((bytecode, _)) = cache::try_load(&EMBEDDED_ZK_DSL, &replacements) {
        println!("(Compilation cache hit)");
        return bytecode;
    }

    let time = Instant::now();
    let source = ProgramSource::Embedded {
        entry: construction.entry().to_string(),
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

fn log2_exact_power_of_two(n: usize) -> usize {
    assert!(n > 0 && n.is_power_of_two());
    n.trailing_zeros() as usize
}

fn generate_codewords(n_blobs: usize) -> Vec<Vec<EF>> {
    let m = 1 << LOG_M;
    let mut rng = StdRng::seed_from_u64(0);
    let mut codewords = Vec::with_capacity(n_blobs);
    for _ in 0..n_blobs {
        let message: Vec<EF> = (0..m).map(|_| rng.random()).collect();
        codewords.push(rs_encode(&message));
    }
    codewords
}

fn push_ext(out: &mut Vec<F>, value: &EF) {
    out.extend_from_slice(<EF as BasedVectorSpace<F>>::as_basis_coefficients_slice(value));
}

fn serialize_codeword_for_witness(codeword: &[EF], construction: Construction) -> Vec<F> {
    let m = 1 << LOG_M;
    let dim = <EF as BasedVectorSpace<F>>::DIMENSION;
    let mut codeword_f = Vec::with_capacity(2 * m * dim);
    match construction {
        Construction::Baseline => {
            for j in 0..m {
                push_ext(&mut codeword_f, &codeword[2 * j]);
            }
            for j in 0..m {
                push_ext(&mut codeword_f, &codeword[2 * j + 1]);
            }
        }
        Construction::OodRow | Construction::OodRowColumnMajor | Construction::OodRowTiled => {
            for value in codeword {
                push_ext(&mut codeword_f, value);
            }
        }
    }
    codeword_f
}

fn serialize_codewords_column_major(codewords: &[Vec<EF>]) -> Vec<F> {
    let dim = <EF as BasedVectorSpace<F>>::DIMENSION;
    let row_len = codewords[0].len();
    let mut out = Vec::with_capacity(codewords.len() * row_len * dim);
    for j in 0..row_len {
        for codeword in codewords {
            push_ext(&mut out, &codeword[j]);
        }
    }
    out
}

fn serialize_codewords_tiled(codewords: &[Vec<EF>]) -> Vec<F> {
    let dim = <EF as BasedVectorSpace<F>>::DIMENSION;
    let tile_len_ext = 64;
    let row_len = codewords[0].len();
    assert_eq!(row_len % tile_len_ext, 0);

    let mut out = Vec::with_capacity(codewords.len() * row_len * dim);
    for tile_start in (0..row_len).step_by(tile_len_ext) {
        for codeword in codewords {
            for e in 0..tile_len_ext {
                push_ext(&mut out, &codeword[tile_start + e]);
            }
        }
    }
    out
}

fn serialize_ext_vec(values: &[EF]) -> Vec<F> {
    let dim = <EF as BasedVectorSpace<F>>::DIMENSION;
    let mut out = Vec::with_capacity(values.len() * dim);
    for value in values {
        push_ext(&mut out, value);
    }
    out
}

fn build_witness_from_codewords(codewords: &[Vec<EF>], construction: Construction) -> ExecutionWitness {
    let mut hints: HashMap<String, Vec<Vec<F>>> = HashMap::new();
    match construction {
        Construction::OodRowColumnMajor => {
            hints.insert(
                "codewords_column_major".to_string(),
                vec![serialize_codewords_column_major(codewords)],
            );
        }
        Construction::OodRowTiled => {
            hints.insert(
                "codewords_tiled".to_string(),
                vec![serialize_codewords_tiled(codewords)],
            );
        }
        Construction::Baseline | Construction::OodRow => {
            let codeword_blobs = codewords
                .iter()
                .map(|codeword| serialize_codeword_for_witness(codeword, construction))
                .collect();
            hints.insert("codeword".to_string(), codeword_blobs);
        }
    }
    ExecutionWitness {
        preamble_memory_len: 0,
        hints,
    }
}

fn build_instance(n_blobs: usize, construction: Construction) -> (ExecutionWitness, Vec<F>) {
    let codewords = generate_codewords(n_blobs);
    match construction {
        Construction::Baseline => {
            let witness = build_witness_from_codewords(&codewords, construction);
            (witness, vec![])
        }
        Construction::OodRow | Construction::OodRowColumnMajor | Construction::OodRowTiled => {
            let public_input = build_ood_public_input(&codewords);
            let witness = build_witness_from_codewords(&codewords, construction);
            (witness, public_input)
        }
    }
}

fn build_ood_public_input(codewords: &[Vec<EF>]) -> Vec<F> {
    let n_blobs = codewords.len();
    let dim = <EF as BasedVectorSpace<F>>::DIMENSION;
    let m = 1 << LOG_M;
    let mut public_input = Vec::with_capacity(n_blobs * 8 + 8 + dim + n_blobs * dim + 8);

    let mut row_digests = Vec::with_capacity(n_blobs);
    for codeword in codewords {
        let mut systematic = Vec::with_capacity(m * dim);
        for value in codeword.iter().take(m) {
            push_ext(&mut systematic, value);
        }
        let digest = utils::poseidon_compress_slice(&systematic, false);
        public_input.extend_from_slice(&digest);
        row_digests.push(digest);
    }

    let chain_digest = chain_digest_array(&row_digests);
    public_input.extend_from_slice(&chain_digest);

    let z_digest = derive_z_digest(&chain_digest);
    public_input.extend_from_slice(&z_digest[..dim]);
    let z = EF::from_basis_coefficients_slice(&z_digest[..dim]).unwrap();

    let row_coeffs = build_scaled_ood_coeffs(n_blobs, z);
    public_input.extend(serialize_ext_vec(&row_coeffs));

    let ood_row = build_scaled_ood_row(codewords, &row_coeffs);
    let ood_root = merkle_root_from_exts(&ood_row);
    public_input.extend_from_slice(&ood_root);

    public_input
}

fn chain_digest_array(digests: &[[F; 8]]) -> [F; 8] {
    let mut state = [F::ZERO; 8];
    for digest in digests {
        state = utils::poseidon16_compress_pair(&state, digest);
    }
    state
}

fn tag_digest(tag: u64) -> [F; 8] {
    let mut digest = [F::ZERO; 8];
    digest[0] = F::from_u64(tag);
    digest
}

fn derive_z_digest(chain_digest: &[F; 8]) -> [F; 8] {
    utils::poseidon16_compress_pair(chain_digest, &tag_digest(1))
}

fn build_scaled_ood_coeffs(n_blobs: usize, z: EF) -> Vec<EF> {
    let log_n_blobs = log2_exact_power_of_two(n_blobs);
    let row_root_inv = EF::from(F::two_adic_generator(log_n_blobs).inverse());
    let numerator = z.exp_u64(n_blobs as u64) - EF::ONE;

    let mut row_coeffs = Vec::with_capacity(n_blobs);
    let mut point = EF::ONE;
    for _ in 0..n_blobs {
        let denominator = z * point - EF::ONE;
        row_coeffs.push(numerator / denominator);
        point *= row_root_inv;
    }
    row_coeffs
}

fn build_scaled_ood_row(codewords: &[Vec<EF>], row_coeffs: &[EF]) -> Vec<EF> {
    assert_eq!(codewords.len(), row_coeffs.len());
    let row_len = codewords[0].len();
    let mut ood_row = vec![EF::ZERO; row_len];
    for j in 0..row_len {
        let mut acc = EF::ZERO;
        for (codeword, coeff) in codewords.iter().zip(row_coeffs) {
            acc += codeword[j] * *coeff;
        }
        ood_row[j] = acc;
    }
    ood_row
}

fn merkle_root_from_exts(row: &[EF]) -> [F; 8] {
    let data = serialize_ext_vec(row);
    merkle_root_from_base(&data)
}

fn merkle_root_from_base(data: &[F]) -> [F; 8] {
    let dim = <EF as BasedVectorSpace<F>>::DIMENSION;
    let leaf_len_ext = 1 << 4;
    let leaf_len = leaf_len_ext * dim;
    assert_eq!(data.len() % leaf_len, 0);
    let mut layer: Vec<[F; 8]> = data
        .chunks_exact(leaf_len)
        .map(|leaf| utils::poseidon_compress_slice(leaf, false))
        .collect();
    assert!(layer.len().is_power_of_two());

    while layer.len() > 1 {
        layer = layer
            .chunks_exact(2)
            .map(|pair| utils::poseidon16_compress_pair(&pair[0], &pair[1]))
            .collect();
    }
    layer[0]
}

pub fn prove_lean_da(
    bytecode: &Bytecode,
    public_input: &[F],
    witness: &ExecutionWitness,
    n_blobs: usize,
    construction: Construction,
) -> ExecutionProof {
    const F_BITS: usize = 31;

    let t0 = Instant::now();
    let proof = prove_execution(
        bytecode,
        public_input,
        witness,
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
    println!("Construction:     {}", construction.label());
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
        let bytecode = compile_lean_da_bytecode(DEFAULT_N_BLOBS, Construction::Baseline);
        let (witness, public_input) = build_instance(DEFAULT_N_BLOBS, Construction::Baseline);
        let proof = prove_lean_da(
            &bytecode,
            &public_input,
            &witness,
            DEFAULT_N_BLOBS,
            Construction::Baseline,
        );
        verify_lean_da(&bytecode, &public_input, proof.proof);
    }

    #[test]
    fn test_ood_public_input_shape() {
        let (_witness, public_input) = build_instance(DEFAULT_N_BLOBS, Construction::OodRow);
        let dim = <EF as BasedVectorSpace<F>>::DIMENSION;
        let expected_len = DEFAULT_N_BLOBS * 8 + 8 + dim + DEFAULT_N_BLOBS * dim + 8;
        assert_eq!(public_input.len(), expected_len);

        let (_witness, public_input) = build_instance(DEFAULT_N_BLOBS, Construction::OodRowColumnMajor);
        assert_eq!(public_input.len(), expected_len);

        let (_witness, public_input) = build_instance(DEFAULT_N_BLOBS, Construction::OodRowTiled);
        assert_eq!(public_input.len(), expected_len);
    }

    #[test]
    #[ignore = "runs the full OOD-row proof benchmark path"]
    fn test_compile_prove_verify_ood_row() {
        let bytecode = compile_lean_da_bytecode(DEFAULT_N_BLOBS, Construction::OodRow);
        let (witness, public_input) = build_instance(DEFAULT_N_BLOBS, Construction::OodRow);
        let proof = prove_lean_da(
            &bytecode,
            &public_input,
            &witness,
            DEFAULT_N_BLOBS,
            Construction::OodRow,
        );
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
