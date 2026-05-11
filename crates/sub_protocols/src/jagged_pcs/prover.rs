use backend::*;
use lean_vm::{EF, F};
use tracing::{info_span, instrument};

use super::config::{JaggedConfig, pack_dense, usize_to_bits, usize_to_point};

/// Output of [`jagged_commit`]. Holds the dense polynomial together with the
/// underlying WHIR commitment witness, so that [`jagged_open`] can both
/// evaluate the dense polynomial and forward the final claim to WHIR.
#[derive(Debug)]
pub struct JaggedPcsWitness {
    pub config: JaggedConfig,
    pub dense: MleOwned<EF>,
    pub whir_witness: Witness<EF>,
}

/// One per-column evaluation claim that the prover wants to attest.
///
/// `sub_table_id` and `col_in_sub_table` together identify which column of
/// the sparse jagged polynomial is being claimed; `z_row` is the row
/// evaluation point and `value` is the claim's right-hand side.
///
/// `value` is the claim about the **padded** column `P` -- i.e. the column
/// extended with `padding_value` for every row in `[h_y, 2^{|z_row|})`.
/// Jagged itself only commits the data-only column `D` (zeros past `h_y`),
/// so it internally subtracts the padding contribution
///   `padding_value * mle_of_zeros_then_ones(h_y, z_row)`
/// (or `mle_of_zeros_then_ones(h_y - 1, z_row)` when `is_next`) before the
/// sumcheck. For columns whose padding is zero, set `padding_value = F::ZERO`
/// and the correction is a no-op.
///
/// When `is_next` is true, `value` is the evaluation of the next-MLE
/// `r -> P[succ(r)]` (with the wrap-on-last-row convention).
#[derive(Debug, Clone)]
pub struct JaggedClaim {
    pub sub_table_id: usize,
    pub col_in_sub_table: usize,
    pub z_row: MultilinearPoint<EF>,
    pub value: EF,
    pub is_next: bool,
    pub padding_value: F,
}

impl JaggedClaim {
    /// Number of zeros (`h_y` for regular, `h_y - 1` for next) in the
    /// `mle_of_zeros_then_ones` indicator that captures the padding rows
    /// for this claim.
    pub(crate) fn padding_n_zeros(&self, sub_table_height: usize) -> usize {
        if self.is_next {
            sub_table_height.saturating_sub(1)
        } else {
            sub_table_height
        }
    }

    /// Adjustment to subtract from `value` so that the underlying jagged
    /// claim is about the data-only column `D` rather than the padded `P`.
    pub(crate) fn padding_adjustment(&self, sub_table_height: usize) -> EF {
        if self.padding_value.is_zero() {
            return EF::ZERO;
        }
        let n_zeros = self.padding_n_zeros(sub_table_height);
        let indicator = mle_of_zeros_then_ones::<EF>(n_zeros, &self.z_row);
        EF::from(self.padding_value) * indicator
    }
}

/// Commit to the jagged polynomial defined by `columns`.
///
/// `columns[y][col][row]` is the value at sub-table `y`, column `col` (in
/// `[0, 2^{c_y})`), row `row` (in `[0, h_y)`). The cumulative table areas
/// are absorbed into the Fiat--Shamir transcript as base scalars before the
/// underlying WHIR commit, so the verifier sees them in the clear.
#[instrument(skip_all)]
pub fn jagged_commit(
    config: &JaggedConfig,
    columns: &[Vec<&[F]>],
    prover_state: &mut impl FSProver<EF>,
    whir_config: &WhirConfigBuilder,
) -> JaggedPcsWitness {
    // Build the dense polynomial in row-major-within-sub-table layout.
    let dense_vec = info_span!("Pack dense").in_scope(|| pack_dense(config, columns));
    let actual_data_len = config.total_area();
    let dense = MleOwned::Base(dense_vec);

    // Absorb the cumulative areas (sent in clear). One length-m bit string per area.
    for &area in &config.cumulative_areas {
        prover_state.add_base_scalars(&usize_to_bits(area, config.log_dense_size));
    }

    let whir = WhirConfig::new(whir_config, config.log_dense_size);
    let whir_witness = whir.commit(prover_state, &dense, actual_data_len);

    JaggedPcsWitness {
        config: config.clone(),
        dense,
        whir_witness,
    }
}

/// Open the jagged commitment for a batch of per-column evaluation claims.
///
/// Protocol (fused with WHIR -- no dedicated jagged sumcheck):
///   1. Sample batching coefficients `alpha_j`.
///   2. Combined claim value
///      `v_combined = sum_j alpha_j * (v_j - padding_adjustment_j)`,
///      so the underlying claim is about the data-only column `D` rather
///      than the padded `P`.
///   3. Materialize `F(i) = sum_j alpha_j * f_hat(point_j, i)` over the
///      boolean cube; on cube `i`, only the sub-table containing `i` and
///      only claims attached to that sub-table contribute.
///   4. Hand `(F, v_combined)` to WHIR as a raw weighted statement. WHIR's
///      own initial sumcheck folds `polynomial * F` and the claim
///      `<polynomial, F> = v_combined`, eliminating the dedicated m-round
///      jagged sumcheck (and the `q(i*)` transcript send) that the
///      pre-fusion version required. The verifier mirrors this by passing
///      a BP-based callback that computes `F(i*)` at WHIR's final folding
///      point.
#[instrument(skip_all)]
pub fn jagged_open(
    witness: JaggedPcsWitness,
    claims: &[JaggedClaim],
    prover_state: &mut impl FSProver<EF>,
    whir_config: &WhirConfigBuilder,
) {
    let JaggedPcsWitness {
        config,
        dense,
        whir_witness,
    } = witness;
    let m = config.log_dense_size;

    // 1. Validate each claim's z_row length: it must be enough to address
    // the corresponding sub-table's height.
    for claim in claims {
        let st = config.sub_tables[claim.sub_table_id];
        let needed = log2_ceil_usize(st.height);
        assert!(
            claim.z_row.len() >= needed,
            "claim z_row of length {} too short for sub-table height {} (need >= {needed} bits)",
            claim.z_row.len(),
            st.height,
        );
        assert!(
            claim.col_in_sub_table < 1 << st.log_width,
            "claim col {} out of range for sub-table width {}",
            claim.col_in_sub_table,
            1 << st.log_width,
        );
    }

    // 2. Sample batching alphas (verifier mirrors this exact sequence).
    let alphas: Vec<EF> = (0..claims.len()).map(|_| prover_state.sample()).collect();

    // 3. Combined claim value, adjusted to be about the data-only column `D`
    // rather than the padded `P` (see [`JaggedClaim::padding_adjustment`]).
    let v_combined: EF = alphas
        .iter()
        .zip(claims)
        .map(|(&a, claim)| {
            let h = config.sub_tables[claim.sub_table_id].height;
            a * (claim.value - claim.padding_adjustment(h))
        })
        .sum();

    // 4. Materialize F(i) over the cube of size 2^m. Only valid cells in
    // each sub-table get a non-zero contribution. Fused (regular, next)
    // pairs share the eq(z_row, .) computation.
    let f_evals = info_span!("Materialize F(i)").in_scope(|| materialize_f(&config, claims, &alphas));

    // 5. Hand (F, v_combined) to WHIR as a raw weighted statement. WHIR's
    // initial sumcheck handles `<polynomial, F> = v_combined` as part of
    // its first folding rounds; no separate sumcheck needed.
    let whir = WhirConfig::new(whir_config, m);
    whir.prove_with_extras(
        prover_state,
        vec![],
        vec![RawWeights {
            cube_weights: f_evals,
            claimed_sum: v_combined,
        }],
        whir_witness,
        &dense.by_ref(),
    );
}

/// Compute the cube-evaluation table of `F(i) = sum_j alpha_j * f_hat_j(i)`.
///
/// For a regular claim `j` against column `(y_j, c_j)` at row-point `z_row_j`:
///   `f_hat_j(i)` (on cube) = `eq(z_row_j, row(i)) * eq(z_col_j, col(i)) * 1[i in y_j]`
///
/// For a next-claim, the column's data-only next-MLE `D_next(z_row)` equals
///   `sum_{r in [1, h-1]} eq(z_row, r-1) * column[r]`,
/// so the contribution to `F` is the same outer product as a regular claim,
/// but written one row down (rows `[1, h-1]` indexed by `r-1 in [0, h-2]`).
/// We implement this by shifting the destination offset by one row width
/// and reducing the row count by one.
///
/// When a regular claim and a next-claim share the same column and `z_row`
/// (the common case: paired up/down claims from the AIR sumcheck), the two
/// outer products overlap on rows `[1, h-1)` and can be fused into a single
/// pass with combined row factor
///   `rf[r] = alpha_eq * eq(z_row, r) + alpha_next * eq(z_row, r-1)`
/// (with `eq(z_row, -1) := 0`). This is purely a prover optimization; the
/// resulting `F` is bit-for-bit identical to the unfused version.
fn materialize_f(config: &JaggedConfig, claims: &[JaggedClaim], alphas: &[EF]) -> Vec<EF> {
    let mut f = EF::zero_vec(config.dense_size());
    let (pairs, singletons) = group_paired_claims(claims);

    for &(eq_idx, next_idx) in &pairs {
        write_paired_outer_product(
            &mut f,
            config,
            &claims[eq_idx],
            alphas[eq_idx],
            &claims[next_idx],
            alphas[next_idx],
        );
    }
    for &idx in &singletons {
        write_single_outer_product(&mut f, config, &claims[idx], alphas[idx]);
    }

    f
}

/// Find (regular, next) claim pairs that share column and `z_row` so the
/// F-materialization can fuse them. Returns `(pairs, singletons)` where
/// `pairs[i] = (eq_idx, next_idx)` are indices into `claims` and `singletons`
/// covers everything else (in original order).
fn group_paired_claims(claims: &[JaggedClaim]) -> (Vec<(usize, usize)>, Vec<usize>) {
    use std::collections::HashMap;

    // Bucket by (sub_table_id, col_in_sub_table). Within each bucket we then
    // greedily match each regular claim to a not-yet-matched next-claim with
    // the same z_row and padding_value.
    let mut buckets: HashMap<(usize, usize), Vec<usize>> = HashMap::new();
    for (i, claim) in claims.iter().enumerate() {
        buckets
            .entry((claim.sub_table_id, claim.col_in_sub_table))
            .or_default()
            .push(i);
    }

    let mut pairs: Vec<(usize, usize)> = Vec::new();
    let mut consumed = vec![false; claims.len()];

    for indices in buckets.values() {
        let next_inds: Vec<usize> = indices.iter().copied().filter(|&i| claims[i].is_next).collect();
        for &e in indices.iter().filter(|&&i| !claims[i].is_next) {
            for &n in &next_inds {
                if consumed[n] {
                    continue;
                }
                if claims[e].padding_value != claims[n].padding_value {
                    continue;
                }
                if claims[e].z_row.0 != claims[n].z_row.0 {
                    continue;
                }
                pairs.push((e, n));
                consumed[e] = true;
                consumed[n] = true;
                break;
            }
        }
    }

    let singletons: Vec<usize> = (0..claims.len()).filter(|&i| !consumed[i]).collect();
    (pairs, singletons)
}

/// One outer product into `f` for a single (regular or next) claim. Mirrors
/// the per-claim contribution of the original unfused materialization.
fn write_single_outer_product(f: &mut [EF], config: &JaggedConfig, claim: &JaggedClaim, alpha: EF) {
    let st = config.sub_tables[claim.sub_table_id];
    let base = config.cumulative_areas[claim.sub_table_id];
    let width = 1usize << st.log_width;
    let z_row_eq = eval_eq::<EF>(&claim.z_row);
    let z_col_point = usize_to_point(claim.col_in_sub_table, st.log_width);
    let z_col_eq = eval_eq::<EF>(&z_col_point);

    let (effective_base, effective_rows) = if claim.is_next {
        if st.height < 2 {
            return;
        }
        (base + width, st.height - 1)
    } else {
        (base, st.height)
    };

    f[effective_base..effective_base + effective_rows * width]
        .par_chunks_mut(width)
        .enumerate()
        .for_each(|(r, chunk)| {
            let row_factor = alpha * z_row_eq[r];
            for (c, slot) in chunk.iter_mut().enumerate() {
                *slot += row_factor * z_col_eq[c];
            }
        });
}

/// Fused outer product for a (regular, next) pair that shares column and
/// `z_row`. The combined row factor is
///   `rf[0]        = alpha_eq * eq(z_row, 0)`
///   `rf[r in 1..h] = alpha_eq * eq(z_row, r) + alpha_next * eq(z_row, r-1)`
/// and the outer product `rf[r] * z_col_eq[c]` is written at offset
/// `base + r*width + c` for `r in [0, h)`. This covers `h` row slots with
/// one pass, vs. `2h - 1` row slots in two unfused passes (rows `[1, h-1)`
/// are written by both contributions in the unfused version).
fn write_paired_outer_product(
    f: &mut [EF],
    config: &JaggedConfig,
    claim_eq: &JaggedClaim,
    alpha_eq: EF,
    claim_next: &JaggedClaim,
    alpha_next: EF,
) {
    debug_assert!(!claim_eq.is_next && claim_next.is_next);
    debug_assert_eq!(claim_eq.sub_table_id, claim_next.sub_table_id);
    debug_assert_eq!(claim_eq.col_in_sub_table, claim_next.col_in_sub_table);
    debug_assert_eq!(claim_eq.padding_value, claim_next.padding_value);
    debug_assert_eq!(claim_eq.z_row.0, claim_next.z_row.0);

    let st = config.sub_tables[claim_eq.sub_table_id];
    if st.height == 0 {
        return;
    }
    let base = config.cumulative_areas[claim_eq.sub_table_id];
    let width = 1usize << st.log_width;
    let z_row_eq = eval_eq::<EF>(&claim_eq.z_row);
    let z_col_point = usize_to_point(claim_eq.col_in_sub_table, st.log_width);
    let z_col_eq = eval_eq::<EF>(&z_col_point);

    // Combined row factor of length `st.height`.
    let mut rf: Vec<EF> = Vec::with_capacity(st.height);
    rf.push(alpha_eq * z_row_eq[0]);
    for r in 1..st.height {
        rf.push(alpha_eq * z_row_eq[r] + alpha_next * z_row_eq[r - 1]);
    }

    f[base..base + st.height * width]
        .par_chunks_mut(width)
        .enumerate()
        .for_each(|(r, chunk)| {
            let row_factor = rf[r];
            for (c, slot) in chunk.iter_mut().enumerate() {
                *slot += row_factor * z_col_eq[c];
            }
        });
}
