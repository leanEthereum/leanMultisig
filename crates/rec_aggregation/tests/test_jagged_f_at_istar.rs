//! Validates the multi-claim F(i*) summation pattern that the recursion
//! verifier needs in `eval_extras_at_final` once jagged is fused with WHIR.
//!
//! Configuration (matches the constants in `test_jagged_f_at_istar.py`):
//!   * single sub-table, log_width = 2 (4 columns), height = 64 (so the
//!     sub-table area is 256, fitting in `log_dense_size = 8`),
//!   * claim 0: regular, col = 1,
//!   * claim 1: is_next, col = 3.
//!
//! Ground truth comes from running `BranchingProgram::eval` twice (once
//! with t_prev = cumulative_areas[0] and once with the shifted version
//! used for is_next claims) and computing `alpha_0 * bp_0 + alpha_1 * bp_1`.

use std::collections::{BTreeMap, HashMap};

use backend::*;
use lean_compiler::*;
use lean_vm::{EF, ExecutionWitness, F, execute_bytecode};
use rand::{RngExt, SeedableRng, rngs::StdRng};
use rec_aggregation::{NUM_REPEATED_ONES, PREAMBLE_MEMORY_LEN, ZERO_VEC_LEN};
use sub_protocols::jagged_pcs::BranchingProgram;

const M_LOG_DENSE: usize = 8;
const LOG_WIDTH: usize = 2;
const Z_ROW_LEN: usize = M_LOG_DENSE - LOG_WIDTH;
const HEIGHT: usize = 64; // 2^Z_ROW_LEN
const COL_0: usize = 1;
const COL_1: usize = 3;

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

fn usize_to_bits_be(value: usize, n_bits: usize) -> Vec<F> {
    (0..n_bits)
        .rev()
        .map(|i| F::from_u32(((value >> i) & 1) as u32))
        .collect()
}

fn usize_to_point(value: usize, n_bits: usize) -> Vec<EF> {
    (0..n_bits)
        .rev()
        .map(|i| if (value >> i) & 1 == 1 { EF::ONE } else { EF::ZERO })
        .collect()
}

#[test]
fn test_jagged_f_at_istar() {
    let path = format!("{}/tests/test_jagged_f_at_istar.py", env!("CARGO_MANIFEST_DIR"));
    let replacements = BTreeMap::from([
        ("ZERO_VEC_LEN_PLACEHOLDER".to_string(), ZERO_VEC_LEN.to_string()),
        (
            "NUM_REPEATED_ONES_PLACEHOLDER".to_string(),
            NUM_REPEATED_ONES.to_string(),
        ),
    ]);
    let bytecode = compile_program_with_flags(&ProgramSource::Filepath(path), CompilationFlags { replacements });

    let mut rng = StdRng::seed_from_u64(0xd065_b4e5);

    // Sub-table cumulative-area layout: [0, HEIGHT * 2^LOG_WIDTH, ...].
    // We only need t_prev for sub-table 0 (= 0) and t_next (= HEIGHT *
    // 2^LOG_WIDTH = 256 = 2^M_LOG_DENSE). The shifted t_prev for
    // is_next is `0 + 2^LOG_WIDTH = 4`.
    let t_prev_int: usize = 0;
    let t_next_int: usize = HEIGHT * (1 << LOG_WIDTH);
    assert_eq!(t_next_int, 1 << M_LOG_DENSE);
    let t_prev_shifted_int: usize = t_prev_int + (1 << LOG_WIDTH);

    let t_prev_bits = usize_to_bits_be(t_prev_int, M_LOG_DENSE);
    let t_prev_shifted_bits = usize_to_bits_be(t_prev_shifted_int, M_LOG_DENSE);
    let t_next_bits = usize_to_bits_be(t_next_int, M_LOG_DENSE);
    // Bits-as-EFs for the Rust BP.
    let t_prev_ef: Vec<EF> = t_prev_bits.iter().map(|&b| EF::from(b)).collect();
    let t_prev_shifted_ef: Vec<EF> = t_prev_shifted_bits.iter().map(|&b| EF::from(b)).collect();
    let t_next_ef: Vec<EF> = t_next_bits.iter().map(|&b| EF::from(b)).collect();

    // Random per-claim z_row, the shared i*, and the alphas.
    let z_row_0: Vec<EF> = (0..Z_ROW_LEN).map(|_| EF::from_u32(rng.random::<u32>())).collect();
    let z_row_1: Vec<EF> = (0..Z_ROW_LEN).map(|_| EF::from_u32(rng.random::<u32>())).collect();
    let z_index: Vec<EF> = (0..M_LOG_DENSE).map(|_| EF::from_u32(rng.random::<u32>())).collect();
    let alpha_0 = EF::from_u32(rng.random::<u32>());
    let alpha_1 = EF::from_u32(rng.random::<u32>());

    let z_col_0 = usize_to_point(COL_0, LOG_WIDTH);
    let z_col_1 = usize_to_point(COL_1, LOG_WIDTH);

    let bp_0 = BranchingProgram::<EF> {
        z_row: &z_row_0,
        z_col: &z_col_0,
        z_index: &z_index,
        log_width: LOG_WIDTH,
        log_dense_size: M_LOG_DENSE,
    }
    .eval(&t_prev_ef, &t_next_ef);
    let bp_1 = BranchingProgram::<EF> {
        z_row: &z_row_1,
        z_col: &z_col_1,
        z_index: &z_index,
        log_width: LOG_WIDTH,
        log_dense_size: M_LOG_DENSE,
    }
    .eval(&t_prev_shifted_ef, &t_next_ef);
    let expected = alpha_0 * bp_0 + alpha_1 * bp_1;

    // Public input: just zeros (DIGEST_LEN).
    let public_input = vec![F::ZERO; 8];

    let mut hints: HashMap<String, Vec<Vec<F>>> = HashMap::new();
    hints.insert("z_row_0".to_string(), vec![efs_to_base(&z_row_0)]);
    hints.insert("z_row_1".to_string(), vec![efs_to_base(&z_row_1)]);
    hints.insert("z_index".to_string(), vec![efs_to_base(&z_index)]);
    hints.insert("t_prev_bits".to_string(), vec![t_prev_bits]);
    hints.insert("t_prev_shifted_bits".to_string(), vec![t_prev_shifted_bits]);
    hints.insert("t_next_bits".to_string(), vec![t_next_bits]);
    hints.insert("alpha_0".to_string(), vec![ef_to_base(&alpha_0)]);
    hints.insert("alpha_1".to_string(), vec![ef_to_base(&alpha_1)]);
    hints.insert("expected".to_string(), vec![ef_to_base(&expected)]);

    let witness = ExecutionWitness {
        preamble_memory_len: PREAMBLE_MEMORY_LEN,
        hints,
    };
    execute_bytecode(&bytecode, &public_input, &witness, false);
}
