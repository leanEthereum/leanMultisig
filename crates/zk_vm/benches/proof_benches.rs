use std::marker::PhantomData;

use compiler::compile_program;
use criterion::{Criterion, black_box, criterion_group, criterion_main};
use pcs::WhirBatchPcs;
use utils::{MyMerkleCompress, MyMerkleHash, build_merkle_compress, build_merkle_hash};
use vm::{EF, F};
use whir_p3::whir::config::{FoldingFactor, SecurityAssumption, WhirConfigBuilder};

use zk_vm::{prove_execution::prove_execution, verify_execution::verify_execution};

fn pcs_builders_for_execution() -> WhirBatchPcs<F, EF, EF, MyMerkleHash, MyMerkleCompress, 8> {
    let base_pcs = WhirConfigBuilder {
        folding_factor: FoldingFactor::ConstantFromSecondRound(7, 4),
        soundness_type: SecurityAssumption::CapacityBound,
        merkle_hash: build_merkle_hash(),
        merkle_compress: build_merkle_compress(),
        pow_bits: 16,
        max_num_variables_to_send_coeffs: 6,
        rs_domain_initial_reduction_factor: 5,
        security_level: 128,
        starting_log_inv_rate: 1,
        base_field: PhantomData::<F>,
        extension_field: PhantomData::<EF>,
    };

    let extension_pcs = WhirConfigBuilder {
        folding_factor: FoldingFactor::ConstantFromSecondRound(4, 4),
        soundness_type: SecurityAssumption::CapacityBound,
        merkle_hash: build_merkle_hash(),
        merkle_compress: build_merkle_compress(),
        pow_bits: 16,
        max_num_variables_to_send_coeffs: 6,
        rs_domain_initial_reduction_factor: 2,
        security_level: 128,
        starting_log_inv_rate: 1,
        base_field: PhantomData::<EF>,
        extension_field: PhantomData::<EF>,
    };

    WhirBatchPcs(base_pcs, extension_pcs)
}

fn build_program_chain(steps: usize) -> String {
    let mut prog = String::from("fn main() {\n");
    // Add enough Poseidon calls to avoid empty packed layers (SIMD width)
    for _ in 0..8 {
        prog.push_str("_ = poseidon16(pointer_to_zero_vector, pointer_to_zero_vector);\n");
    }
    for _ in 0..8 {
        prog.push_str("_ = poseidon24(pointer_to_zero_vector, pointer_to_zero_vector);\n");
    }
    prog.push_str("a0 = 0;\n");
    for i in 1..=steps {
        prog.push_str(&format!("a{i} = a{} + 1;\n", i - 1));
    }
    prog.push_str("return;\n}\n");
    prog
}

fn bench_proof(c: &mut Criterion) {
    // Prepare inputs once
    // Build a straight-line program with many assignments (no loops/ifs)
    let program = build_program_chain(700);
    let bytecode = compile_program(&program);
    let public_input: Vec<F> = vec![];
    let batch_pcs = pcs_builders_for_execution();

    // Compute a single proof to report size and serve verification input
    let proof_data_once = prove_execution(&bytecode, &public_input, &[], &batch_pcs);
    let elems = proof_data_once.len();
    let approx_bytes = elems as u64 * 4; // KoalaBear ~31-bit => ~4 bytes/elem
    println!("proof size: {} elems (~{} bytes)", elems, approx_bytes);

    let mut group = c.benchmark_group("zk_proof");
    group.sample_size(10);

    group.bench_function("prove_execution", |b| {
        b.iter(|| {
            let _ = prove_execution(
                black_box(&bytecode),
                black_box(&public_input),
                black_box(&[]),
                black_box(&batch_pcs),
            );
        })
    });

    group.bench_function("verify_execution", |b| {
        b.iter(|| {
            let proof = proof_data_once.clone();
            verify_execution(
                black_box(&bytecode),
                black_box(&public_input),
                black_box(proof),
                black_box(&batch_pcs),
            )
            .unwrap();
        })
    });

    group.finish();
}

criterion_group!(benches, bench_proof);
criterion_main!(benches);
