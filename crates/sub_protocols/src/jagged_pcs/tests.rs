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

/// Evaluate the **data-only next-MLE** of `column` at `z_row`. The data-only
/// column has zeros past `column.len()` (so the wrap term vanishes), giving
/// `D_next_MLE(z) = sum_{r in [1, h-1]} eq(z, r-1) * column[r]`.
fn ground_truth_next_eval(column: &[F], z_row: &MultilinearPoint<EF>) -> EF {
    let n = z_row.len();
    let size = 1usize << n;
    assert!(column.len() <= size);
    let z_eq = eval_eq::<EF>(z_row);
    let mut acc = EF::ZERO;
    for r in 1..column.len() {
        acc += z_eq[r - 1] * column[r];
    }
    acc
}

/// Evaluate the **padded** column's MLE at `z_row`: the data-only column
/// `D` extended with `padding_value` for every row in `[h, 2^|z_row|)`.
/// This is the value that the AIR sumcheck would actually claim.
fn ground_truth_padded_eval(column: &[F], padding_value: F, z_row: &MultilinearPoint<EF>) -> EF {
    let n = z_row.len();
    let size = 1usize << n;
    assert!(column.len() <= size);
    let z_eq = eval_eq::<EF>(z_row);
    let mut acc = EF::ZERO;
    for (i, &v) in column.iter().enumerate() {
        acc += z_eq[i] * v;
    }
    for i in column.len()..size {
        acc += z_eq[i] * padding_value;
    }
    acc
}

/// Evaluate the **padded** column's next-MLE at `z_row`, with our
/// wrap-on-last-row convention (`succ(2^n - 1) = 2^n - 1`). This is the
/// value the AIR sumcheck claims for a down-column.
fn ground_truth_padded_next_eval(column: &[F], padding_value: F, z_row: &MultilinearPoint<EF>) -> EF {
    let n = z_row.len();
    let size = 1usize << n;
    assert!(column.len() <= size);
    let value_at = |r: usize| -> F { if r < column.len() { column[r] } else { padding_value } };
    let z_eq = eval_eq::<EF>(z_row);
    let mut acc = EF::ZERO;
    for r in 0..size {
        let succ = if r + 1 < size { r + 1 } else { r };
        acc += z_eq[r] * value_at(succ);
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
                is_next: false,
                padding_value: F::ZERO,
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
                is_next: false,
                padding_value: F::ZERO,
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

#[test]
fn jagged_next_eval_consistency() {
    // Math-only check: for a mix of regular and next-claims, the prover's
    // F(i*) materialization (via the shifted-row trick for next-claims) must
    // equal the verifier's per-claim BP-sum (with shifted t_prev for
    // next-claims).
    let sub_tables = vec![
        SubTable {
            log_width: 2,
            height: 7,
        },
        SubTable {
            log_width: 1,
            height: 11,
        },
        SubTable {
            log_width: 0,
            height: 23,
        },
    ];
    let config = JaggedConfig::new(sub_tables);

    let mut rng = StdRng::seed_from_u64(0xa5a5_5a5a);
    let owned_columns = random_columns(&mut rng, &config.sub_tables);

    // Mix regular and next-claims for every column.
    let mut claims = Vec::new();
    for (y, st) in config.sub_tables.iter().enumerate() {
        for col in 0..(1 << st.log_width) {
            let n_row_bits = log2_ceil_usize(st.height);
            for &is_next in &[false, true] {
                let z_row = MultilinearPoint(
                    (0..n_row_bits)
                        .map(|_| EF::from_u32(rng.random::<u32>() & 0xffff))
                        .collect(),
                );
                let value = if is_next {
                    ground_truth_next_eval(&owned_columns[y][col], &z_row)
                } else {
                    ground_truth_eval(&owned_columns[y][col], &z_row)
                };
                claims.push(JaggedClaim {
                    sub_table_id: y,
                    col_in_sub_table: col,
                    z_row,
                    value,
                    is_next,
                    padding_value: F::ZERO,
                });
            }
        }
    }

    // Materialize F as the prover would (with the shifted-row layout for
    // next-claims).
    let alphas: Vec<EF> = (0..claims.len()).map(|j| EF::from_u32(0x1234 + j as u32)).collect();
    let mut f = EF::zero_vec(config.dense_size());
    for (claim, &alpha) in claims.iter().zip(&alphas) {
        let st = config.sub_tables[claim.sub_table_id];
        let base = config.cumulative_areas[claim.sub_table_id];
        let width = 1usize << st.log_width;
        let z_row_eq = eval_eq::<EF>(&claim.z_row);
        let z_col_pt = usize_to_point(claim.col_in_sub_table, st.log_width);
        let z_col_eq = eval_eq::<EF>(&z_col_pt);
        let (effective_base, effective_rows) = if claim.is_next {
            if st.height < 2 {
                continue;
            }
            (base + width, st.height - 1)
        } else {
            (base, st.height)
        };
        for r in 0..effective_rows {
            for c in 0..width {
                f[effective_base + r * width + c] += alpha * z_row_eq[r] * z_col_eq[c];
            }
        }
    }

    let m = config.log_dense_size;
    let i_star = MultilinearPoint((0..m).map(|_| EF::from_u32(rng.random::<u32>() & 0xffff)).collect());
    let f_mle = MleOwned::<EF>::Extension(f);
    let direct = f_mle.evaluate(&i_star);

    // Verifier-style: sum of per-claim BP evals with shifted t_prev for next-claims.
    let cumulative_area_bits_ef: Vec<Vec<EF>> = config
        .cumulative_areas
        .iter()
        .map(|&a| usize_to_bits(a, m).into_iter().map(EF::from).collect())
        .collect();
    let mut bp_sum = EF::ZERO;
    for (claim, &alpha) in claims.iter().zip(&alphas) {
        let st = config.sub_tables[claim.sub_table_id];
        let z_col_point = usize_to_point(claim.col_in_sub_table, st.log_width);
        let t_prev_bits: Vec<EF> = if claim.is_next {
            let shifted = config.cumulative_areas[claim.sub_table_id] + (1usize << st.log_width);
            usize_to_bits(shifted, m).into_iter().map(EF::from).collect()
        } else {
            cumulative_area_bits_ef[claim.sub_table_id].clone()
        };
        let bp = BranchingProgram {
            z_row: &claim.z_row,
            z_col: &z_col_point,
            z_index: &i_star,
            log_width: st.log_width,
            log_dense_size: m,
        };
        let bp_eval = bp.eval(&t_prev_bits, &cumulative_area_bits_ef[claim.sub_table_id + 1]);
        bp_sum += alpha * bp_eval;
    }

    assert_eq!(direct, bp_sum, "next-claim F(i*) reconstruction mismatch");
}

#[test]
fn jagged_round_trip_with_whir_including_next_claims() {
    // Same configuration as `jagged_round_trip_with_whir`, but every column
    // generates BOTH a regular and a next-claim. Stresses the wiring of
    // `is_next` through commit/open/verify and WHIR.
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

    let mut rng = StdRng::seed_from_u64(0x0bad_cafe);
    let owned_columns = random_columns(&mut rng, &config.sub_tables);
    let columns: Vec<Vec<&[F]>> = owned_columns
        .iter()
        .map(|st| st.iter().map(|c| c.as_slice()).collect())
        .collect();

    let mut claims = Vec::new();
    for (y, st) in config.sub_tables.iter().enumerate() {
        for col in 0..(1 << st.log_width) {
            let n_row_bits = log2_ceil_usize(st.height);
            for &is_next in &[false, true] {
                let z_row = MultilinearPoint(
                    (0..n_row_bits)
                        .map(|_| EF::from_u32(rng.random::<u32>() & 0xffff))
                        .collect(),
                );
                let value = if is_next {
                    ground_truth_next_eval(&owned_columns[y][col], &z_row)
                } else {
                    ground_truth_eval(&owned_columns[y][col], &z_row)
                };
                claims.push(JaggedClaim {
                    sub_table_id: y,
                    col_in_sub_table: col,
                    z_row,
                    value,
                    is_next,
                    padding_value: F::ZERO,
                });
            }
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

#[test]
fn jagged_round_trip_with_padding_and_next_claims() {
    // Real zkVM situation: each column has a non-zero `padding_value` and
    // the AIR claim is about the *padded* column's MLE at z_row of length
    // log2(padded_size). The data committed by jagged is the data-only
    // column (no padding values). Per claim, jagged subtracts
    // padding_value * mle_of_zeros_then_ones(h or h-1, z_row) before the
    // sumcheck, so the verifier accepts only when both sides agree.
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

    let whir_config = small_whir_config();

    let mut rng = StdRng::seed_from_u64(0xc0ff_eeee);
    let owned_columns = random_columns(&mut rng, &config.sub_tables);
    let columns: Vec<Vec<&[F]>> = owned_columns
        .iter()
        .map(|st| st.iter().map(|c| c.as_slice()).collect())
        .collect();

    // One non-zero padding value per (sub_table, col), simulating what
    // execution/extension_op/poseidon's `padding_row` produces. Most
    // columns in real use have padding_value = 0; we deliberately use
    // non-zero for ALL columns here to stress the correction path.
    let padding_values: Vec<Vec<F>> = config
        .sub_tables
        .iter()
        .enumerate()
        .map(|(y, st)| {
            (0..(1 << st.log_width))
                .map(|col| F::from_usize(7 + 13 * y + 31 * col))
                .collect()
        })
        .collect();

    // The AIR z_row has length log2(padded_size). We pick a padded size
    // strictly larger than every sub-table's height so the padding region
    // is non-empty for all of them.
    let padded_log_size = config
        .sub_tables
        .iter()
        .map(|st| log2_ceil_usize(st.height + 1))
        .max()
        .unwrap()
        .max(log2_ceil_usize(config.sub_tables.iter().map(|st| st.height).max().unwrap()) + 1);

    let mut claims = Vec::new();
    for (y, st) in config.sub_tables.iter().enumerate() {
        for col in 0..(1 << st.log_width) {
            for &is_next in &[false, true] {
                // z_row at the padded length.
                let z_row = MultilinearPoint(
                    (0..padded_log_size)
                        .map(|_| EF::from_u32(rng.random::<u32>() & 0xffff))
                        .collect(),
                );
                let pv = padding_values[y][col];
                let value = if is_next {
                    ground_truth_padded_next_eval(&owned_columns[y][col], pv, &z_row)
                } else {
                    ground_truth_padded_eval(&owned_columns[y][col], pv, &z_row)
                };
                claims.push(JaggedClaim {
                    sub_table_id: y,
                    col_in_sub_table: col,
                    z_row,
                    value,
                    is_next,
                    padding_value: pv,
                });
            }
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

#[test]
fn jagged_padding_correction_rejects_wrong_padding_value() {
    // Soundness sanity: if the prover/verifier disagree on padding_value
    // for any one claim, verification must fail.
    let sub_tables = vec![SubTable {
        log_width: 0,
        height: 1500,
    }];
    let config = JaggedConfig::new(sub_tables);
    let whir_config = small_whir_config();

    let mut rng = StdRng::seed_from_u64(0x0bad_0bad);
    let owned_columns = random_columns(&mut rng, &config.sub_tables);
    let columns: Vec<Vec<&[F]>> = owned_columns
        .iter()
        .map(|st| st.iter().map(|c| c.as_slice()).collect())
        .collect();

    // Need log_dense_size >= 17 to satisfy the WHIR config; pad config
    // synthetically with a second sub-table.
    if config.log_dense_size < 17 {
        return;
    }

    let padding_value = F::from_u32(42);
    let z_row = MultilinearPoint(
        (0..log2_ceil_usize(2000))
            .map(|_| EF::from_u32(rng.random::<u32>() & 0xffff))
            .collect(),
    );
    let value = ground_truth_padded_eval(&owned_columns[0][0], padding_value, &z_row);

    let prover_claim = JaggedClaim {
        sub_table_id: 0,
        col_in_sub_table: 0,
        z_row: z_row.clone(),
        value,
        is_next: false,
        padding_value,
    };
    let mut verifier_claim = prover_claim.clone();
    verifier_claim.padding_value = F::from_u32(43); // disagree

    precompute_dft_twiddles::<F>(1 << F::TWO_ADICITY);
    let mut prover_state = build_prover_state();
    let witness = jagged_commit(&config, &columns, &mut prover_state, &whir_config);
    jagged_open(witness, &[prover_claim], &mut prover_state, &whir_config);

    let mut verifier_state = build_verifier_state(prover_state).expect("verifier state");
    let parsed = jagged_parse_commitment(&config, &mut verifier_state, &whir_config).expect("parse");
    let err = jagged_verify(&config, &parsed, &[verifier_claim], &mut verifier_state, &whir_config);
    assert!(err.is_err(), "verification must fail when padding_value disagrees");
}

#[test]
fn jagged_padding_math_isolated() {
    // Direct check of the claimed identity:
    //   P(z) - padding_value * mle_of_zeros_then_ones(h, z) == D(z)
    // and the next-claim variant
    //   P_next(z) - padding_value * mle_of_zeros_then_ones(h-1, z) == D_next(z)
    // for a single small column. This is independent of jagged itself.
    let mut rng = StdRng::seed_from_u64(0x42_42_42);
    let h = 5usize;
    let log_padded = 4usize; // padded size = 16
    let padding_value = F::from_u32(7);

    let column: Vec<F> = (0..h).map(|_| F::from_u32(rng.random::<u32>() & 0xff)).collect();
    let z_row = MultilinearPoint(
        (0..log_padded)
            .map(|_| EF::from_u32(rng.random::<u32>() & 0xffff))
            .collect(),
    );

    // P(z) = padded eval, D(z) = data-only eval.
    let p_eval = ground_truth_padded_eval(&column, padding_value, &z_row);
    let d_eval = ground_truth_eval(&column, &z_row);

    let indicator_padded = mle_of_zeros_then_ones::<EF>(h, &z_row);
    assert_eq!(
        p_eval - EF::from(padding_value) * indicator_padded,
        d_eval,
        "regular padding correction wrong"
    );

    // P_next(z) - k * mle_of_zeros_then_ones(h-1, z) == D_next(z).
    let p_next_eval = ground_truth_padded_next_eval(&column, padding_value, &z_row);
    let d_next_eval = ground_truth_next_eval(&column, &z_row);

    let indicator_next = mle_of_zeros_then_ones::<EF>(h - 1, &z_row);
    assert_eq!(
        p_next_eval - EF::from(padding_value) * indicator_next,
        d_next_eval,
        "next-claim padding correction wrong"
    );
}
