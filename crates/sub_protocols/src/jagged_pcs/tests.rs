//! End-to-end tests for the fancy jagged PCS.
#![allow(clippy::needless_range_loop)]

//!
//! The protocol-level test (`jagged_round_trip_with_whir`) commits to a
//! random small jagged polynomial via WHIR, opens a batch of randomly
//! sampled per-column claims, and verifies the proof. It catches transcript
//! / sumcheck / branching-program / WHIR-statement mismatches end-to-end.
//!
//! The math-only test (`jagged_eval_consistency`) directly checks that the
//! verifier-side reconstruction of `F(i*)` from per-claim BP evaluations
//! agrees with the prover-side materialization of `F(i)` evaluated at `i*`,
//! independent of WHIR / Fiat-Shamir wiring.

use backend::*;
use lean_vm::{EF, F};
use rand::{RngExt, SeedableRng, rngs::StdRng};
use utils::{build_prover_state, build_verifier_state};

use super::branching::BranchingProgram;
use super::config::{JaggedConfig, SubTable, usize_to_bits, usize_to_point};
use super::prover::{JaggedClaim, jagged_commit, jagged_open};
use super::verifier::{jagged_parse_commitment, jagged_verify};

fn small_whir_config() -> WhirConfigBuilder {
    // Mirrors the working WhirConfigBuilder used by
    // `crates/sub_protocols/tests/prove_poseidon_16.rs`. Real proofs go
    // through `lean_prover::default_whir_config`.
    WhirConfigBuilder {
        folding_factor: FoldingFactor::new(7, 4),
        soundness_type: SecurityAssumption::JohnsonBound,
        pow_bits: 0,
        max_num_variables_to_send_coeffs: 9,
        rs_domain_initial_reduction_factor: 5,
        security_level: 80,
        starting_log_inv_rate: 1,
    }
}

fn random_columns(rng: &mut StdRng, sub_tables: &[SubTable]) -> Vec<Vec<Vec<F>>> {
    sub_tables
        .iter()
        .map(|st| {
            let width = 1usize << st.log_width;
            (0..width)
                .map(|_| {
                    (0..st.height)
                        .map(|_| F::from_u32(rng.random::<u32>() & 0xffff))
                        .collect::<Vec<_>>()
                })
                .collect()
        })
        .collect()
}

/// Evaluate the sparse jagged polynomial at `(z_tab=binary(y), z_row, z_col=binary(col))`
/// directly, by enumerating the cube. Used as the ground-truth value for
/// the per-column evaluation claims fed into the protocol.
fn ground_truth_eval(column: &[F], z_row: &MultilinearPoint<EF>) -> EF {
    // Treat the column as a multilinear polynomial in `z_row.len()` variables
    // with the column entries as cube evaluations (zero-padded past `len`).
    let n = z_row.len();
    let size = 1usize << n;
    assert!(column.len() <= size);
    let z_eq = eval_eq::<EF>(z_row);
    let mut acc = EF::ZERO;
    for (i, &v) in column.iter().enumerate() {
        acc += z_eq[i] * v;
    }
    acc
}

#[test]
fn jagged_eval_consistency() {
    // Pick small heterogeneous sub-tables.
    let sub_tables = vec![
        SubTable {
            log_width: 2,
            height: 5,
        }, // 4 cols, 5 rows
        SubTable {
            log_width: 3,
            height: 9,
        }, // 8 cols, 9 rows
        SubTable {
            log_width: 0,
            height: 17,
        }, // 1 col, 17 rows
    ];
    let config = JaggedConfig::new(sub_tables);

    let mut rng = StdRng::seed_from_u64(0x1234_5678);
    let owned_columns = random_columns(&mut rng, &config.sub_tables);

    // Pick claims targeting the actual columns at random row points.
    let mut claims = Vec::new();
    for (y, st) in config.sub_tables.iter().enumerate() {
        for col in 0..(1 << st.log_width) {
            let n_row_bits = log2_ceil_usize(st.height);
            let z_row = MultilinearPoint(
                (0..n_row_bits)
                    .map(|_| EF::from_u32(rng.random::<u32>() & 0xffff))
                    .collect(),
            );
            let value = ground_truth_eval(&owned_columns[y][col], &z_row);
            claims.push(JaggedClaim {
                sub_table_id: y,
                col_in_sub_table: col,
                z_row,
                value,
            });
        }
    }

    // Materialize F as the prover would.
    let alphas: Vec<EF> = (0..claims.len())
        .map(|j| EF::from_u32(0xdead_beef + j as u32))
        .collect();
    let mut f = EF::zero_vec(config.dense_size());
    for (claim, &alpha) in claims.iter().zip(&alphas) {
        let st = config.sub_tables[claim.sub_table_id];
        let base = config.cumulative_areas[claim.sub_table_id];
        let width = 1usize << st.log_width;
        let z_row_eq = eval_eq::<EF>(&claim.z_row);
        let z_col_pt = usize_to_point(claim.col_in_sub_table, st.log_width);
        let z_col_eq = eval_eq::<EF>(&z_col_pt);
        for r in 0..st.height {
            for c in 0..width {
                f[base + r * width + c] += alpha * z_row_eq[r] * z_col_eq[c];
            }
        }
    }

    // Pick a random i* in F^m and compare the two ways of evaluating F(i*).
    let m = config.log_dense_size;
    let i_star = MultilinearPoint((0..m).map(|_| EF::from_u32(rng.random::<u32>() & 0xffff)).collect());
    let f_mle = MleOwned::<EF>::Extension(f);
    let direct = f_mle.evaluate(&i_star);

    // Verifier-style: sum of per-claim BP evals.
    let cumulative_area_bits_ef: Vec<Vec<EF>> = config
        .cumulative_areas
        .iter()
        .map(|&a| usize_to_bits(a, m).into_iter().map(EF::from).collect())
        .collect();
    let mut bp_sum = EF::ZERO;
    for (claim, &alpha) in claims.iter().zip(&alphas) {
        let st = config.sub_tables[claim.sub_table_id];
        let z_col_point = usize_to_point(claim.col_in_sub_table, st.log_width);
        let bp = BranchingProgram {
            z_row: &claim.z_row,
            z_col: &z_col_point,
            z_index: &i_star,
            log_width: st.log_width,
            log_dense_size: m,
        };
        let bp_eval = bp.eval(
            &cumulative_area_bits_ef[claim.sub_table_id],
            &cumulative_area_bits_ef[claim.sub_table_id + 1],
        );
        bp_sum += alpha * bp_eval;
    }

    assert_eq!(direct, bp_sum, "F(i*) reconstruction mismatch");
}

#[test]
fn jagged_round_trip_with_whir() {
    // Sub-tables sized so the dense polynomial is around 2^17, large enough
    // for the (7, 4) WHIR folding factor with at least one inner round
    // (need num_variables > first_round + max_num_variables_to_send_coeffs
    // = 7 + 9 = 16, so log_dense_size >= 17).
    let sub_tables = vec![
        SubTable {
            log_width: 3,
            height: 8000,
        },
        SubTable {
            log_width: 2,
            height: 12000,
        },
        SubTable {
            log_width: 0,
            height: 1500,
        },
    ];
    let config = JaggedConfig::new(sub_tables);
    assert!(config.log_dense_size >= 17);

    let whir_config = small_whir_config();

    let mut rng = StdRng::seed_from_u64(0xfeed_face);
    let owned_columns = random_columns(&mut rng, &config.sub_tables);
    let columns: Vec<Vec<&[F]>> = owned_columns
        .iter()
        .map(|st| st.iter().map(|c| c.as_slice()).collect())
        .collect();

    // Build claims for every column.
    let mut claims = Vec::new();
    for (y, st) in config.sub_tables.iter().enumerate() {
        for col in 0..(1 << st.log_width) {
            let n_row_bits = log2_ceil_usize(st.height);
            let z_row = MultilinearPoint(
                (0..n_row_bits)
                    .map(|_| EF::from_u32(rng.random::<u32>() & 0xffff))
                    .collect(),
            );
            let value = ground_truth_eval(&owned_columns[y][col], &z_row);
            claims.push(JaggedClaim {
                sub_table_id: y,
                col_in_sub_table: col,
                z_row,
                value,
            });
        }
    }

    precompute_dft_twiddles::<F>(1 << F::TWO_ADICITY);
    let mut prover_state = build_prover_state();
    let witness = jagged_commit(&config, &columns, &mut prover_state, &whir_config);
    jagged_open(witness, &claims, &mut prover_state, &whir_config);

    let mut verifier_state = build_verifier_state(prover_state).expect("verifier state");
    let parsed = jagged_parse_commitment(&config, &mut verifier_state, &whir_config).expect("parse");
    jagged_verify(&config, &parsed, &claims, &mut verifier_state, &whir_config).expect("verify");
}
