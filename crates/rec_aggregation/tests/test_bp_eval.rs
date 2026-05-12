//! Validation test for the zkDSL `bp_eval` (in
//! `crates/rec_aggregation/zkdsl_implem/jagged_bp.py`) against the Rust
//! ground-truth
//! [`sub_protocols::jagged_pcs::BranchingProgram::eval`].
//!
//! For random points `(z_row, z_col, z_index, t_prev, t_next)`, we
//! (1) compute the Rust BP eval result (verifier-side ground truth),
//! (2) encode the four scalar sizes into the public input and the EF
//! arrays into witness hints, (3) compile and run the zkDSL
//! `test_bp_eval.py` program, which calls `bp_eval` and `assert`s the
//! result matches `expected`. Any mismatch causes the zkDSL `assert`
//! (write-once memory) to fire and the test panics.

use std::collections::{BTreeMap, HashMap};

use backend::*;
use lean_compiler::*;
use lean_vm::{EF, ExecutionWitness, F, execute_bytecode};
use rand::{RngExt, SeedableRng, rngs::StdRng};
use rec_aggregation::{NUM_REPEATED_ONES, PREAMBLE_MEMORY_LEN, ZERO_VEC_LEN};
use sub_protocols::jagged_pcs::BranchingProgram;

fn ef_to_base(x: &EF) -> Vec<F> {
    x.as_basis_coefficients_slice().to_vec()
}

fn efs_to_base(xs: &[EF]) -> Vec<F> {
    let mut out = Vec::with_capacity(xs.len() * 5);
    for x in xs {
        out.extend_from_slice(x.as_basis_coefficients_slice());
    }
    out
}

#[test]
fn test_bp_eval_matches_rust() {
    let path = format!("{}/tests/test_bp_eval.py", env!("CARGO_MANIFEST_DIR"));
    let replacements = BTreeMap::from([
        ("ZERO_VEC_LEN_PLACEHOLDER".to_string(), ZERO_VEC_LEN.to_string()),
        (
            "NUM_REPEATED_ONES_PLACEHOLDER".to_string(),
            NUM_REPEATED_ONES.to_string(),
        ),
    ]);
    let bytecode = compile_program_with_flags(&ProgramSource::Filepath(path), CompilationFlags { replacements });

    let mut rng = StdRng::seed_from_u64(0xb47_eea1);

    // Each test case stages its own hints + public input and runs once.
    // Keeping log_dense_size modest (~14) keeps each zkDSL execution fast.
    let n_samples = 20;
    let mut z_row_hints: Vec<Vec<F>> = Vec::with_capacity(n_samples);
    let mut z_col_hints: Vec<Vec<F>> = Vec::with_capacity(n_samples);
    let mut z_index_hints: Vec<Vec<F>> = Vec::with_capacity(n_samples);
    let mut t_prev_hints: Vec<Vec<F>> = Vec::with_capacity(n_samples);
    let mut t_next_hints: Vec<Vec<F>> = Vec::with_capacity(n_samples);
    let mut expected_hints: Vec<Vec<F>> = Vec::with_capacity(n_samples);
    let mut public_inputs: Vec<Vec<F>> = Vec::with_capacity(n_samples);

    for sample_idx in 0..n_samples {
        let log_dense_size: usize = rng.random_range(8usize..=14);
        let max_lw = 4.min(log_dense_size);
        let log_width: usize = rng.random_range(0usize..=max_lw);
        // Every third sample exercises the z_row_correction MSB-product
        // branch (z_row longer than the BP reads).
        let z_row_len: usize = if sample_idx % 3 == 0 && log_dense_size > log_width {
            log_dense_size - log_width + rng.random_range(1usize..=3)
        } else {
            log_dense_size.saturating_sub(log_width)
        };
        let z_col_len: usize = log_width;

        let z_row: Vec<EF> = (0..z_row_len).map(|_| EF::from_u32(rng.random::<u32>())).collect();
        let z_col: Vec<EF> = (0..z_col_len).map(|_| EF::from_u32(rng.random::<u32>())).collect();
        let z_index: Vec<EF> = (0..log_dense_size).map(|_| EF::from_u32(rng.random::<u32>())).collect();
        let t_prev: Vec<EF> = (0..log_dense_size)
            .map(|_| {
                if rng.random::<u32>() & 1 == 1 {
                    EF::ONE
                } else {
                    EF::ZERO
                }
            })
            .collect();
        let t_next: Vec<EF> = (0..log_dense_size)
            .map(|_| {
                if rng.random::<u32>() & 1 == 1 {
                    EF::ONE
                } else {
                    EF::ZERO
                }
            })
            .collect();

        let bp = BranchingProgram::<EF> {
            z_row: &z_row,
            z_col: &z_col,
            z_index: &z_index,
            log_width,
            log_dense_size,
        };
        let expected = bp.eval(&t_prev, &t_next);

        // Public input: 4 scalars + 4 zeros pad = DIGEST_LEN.
        let mut pi: Vec<F> = vec![
            F::from_usize(log_width),
            F::from_usize(log_dense_size),
            F::from_usize(z_row_len),
            F::from_usize(z_col_len),
        ];
        while pi.len() < 8 {
            pi.push(F::ZERO);
        }

        public_inputs.push(pi);
        z_row_hints.push(efs_to_base(&z_row));
        z_col_hints.push(efs_to_base(&z_col));
        z_index_hints.push(efs_to_base(&z_index));
        t_prev_hints.push(efs_to_base(&t_prev));
        t_next_hints.push(efs_to_base(&t_next));
        expected_hints.push(ef_to_base(&expected));
    }

    for i in 0..n_samples {
        let mut hints: HashMap<String, Vec<Vec<F>>> = HashMap::new();
        hints.insert("z_row".to_string(), vec![z_row_hints[i].clone()]);
        hints.insert("z_col".to_string(), vec![z_col_hints[i].clone()]);
        hints.insert("z_index".to_string(), vec![z_index_hints[i].clone()]);
        hints.insert("t_prev".to_string(), vec![t_prev_hints[i].clone()]);
        hints.insert("t_next".to_string(), vec![t_next_hints[i].clone()]);
        hints.insert("expected".to_string(), vec![expected_hints[i].clone()]);
        let witness = ExecutionWitness {
            preamble_memory_len: PREAMBLE_MEMORY_LEN,
            hints,
        };
        execute_bytecode(&bytecode, &public_inputs[i], &witness, false);
    }
}
