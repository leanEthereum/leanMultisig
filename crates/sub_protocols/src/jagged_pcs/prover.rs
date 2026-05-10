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
/// the sparse jagged polynomial is being claimed, while `z_row` is the
/// row-evaluation point and `value` is the claimed evaluation.
#[derive(Debug, Clone)]
pub struct JaggedClaim {
    pub sub_table_id: usize,
    pub col_in_sub_table: usize,
    pub z_row: MultilinearPoint<EF>,
    pub value: EF,
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
/// Protocol:
///   1. Sample batching coefficients `alpha_j` and reduce the K claims to a
///      single sumcheck of `sum_i q(i) * F(i) = sum_j alpha_j * v_j`.
///   2. Prover materializes `F(i) = sum_j alpha_j * f_hat(point_j, i)` over
///      the boolean cube; on cube `i`, only the unique sub-table containing
///      `i` and only claims attached to that sub-table contribute.
///   3. Run a product sumcheck reducing `(q, F)` to a single point `i*`.
///   4. Send `q(i*)` so the verifier can decouple `q(i*) * F(i*)` and
///      compute `F(i*)` itself by evaluating the width-6 branching program
///      once per claim.
///   5. Forward the dense claim `q(i*) = ?` to the underlying WHIR.
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

    // 2. Sample batching alphas.
    let alphas: Vec<EF> = (0..claims.len()).map(|_| prover_state.sample()).collect();

    // 3. Combined claim value.
    let v_combined: EF = alphas.iter().zip(claims).map(|(&a, claim)| a * claim.value).sum();

    // 4. Materialize F(i) over the cube of size 2^m. Only valid cells in
    // each sub-table get a non-zero contribution.
    let f_evals = info_span!("Materialize F(i)").in_scope(|| materialize_f(&config, claims, &alphas));
    let f_mle = MleOwned::Extension(f_evals);

    // 5. Run the product sumcheck.
    let dense_ref = dense.by_ref();
    let f_ref = f_mle.by_ref();
    let (sumcheck_point, sumcheck_value, _q_folded, _f_folded) = info_span!("Jagged product sumcheck")
        .in_scope(|| run_product_sumcheck(&dense_ref, &f_ref, prover_state, v_combined, m, 0));

    // 6. Send q(i*) so the verifier can split sumcheck_value = q(i*) * F(i*).
    let q_at_istar = dense.evaluate(&sumcheck_point);
    prover_state.add_extension_scalars(&[q_at_istar]);
    debug_assert_eq!(
        sumcheck_value,
        q_at_istar * f_mle.evaluate(&sumcheck_point),
        "sumcheck value should equal q(i*) * F(i*)"
    );

    // 7. Forward the dense claim to WHIR.
    let stmt = SparseStatement::dense(sumcheck_point, q_at_istar);
    let whir = WhirConfig::new(whir_config, m);
    whir.prove(prover_state, vec![stmt], whir_witness, &dense.by_ref());
}

/// Compute the cube-evaluation table of F(i) =
/// `sum_j alpha_j * eq(z_row_j, row(i)) * eq(z_col_j, col(i)) * 1[i in sub_table y_j]`.
fn materialize_f(config: &JaggedConfig, claims: &[JaggedClaim], alphas: &[EF]) -> Vec<EF> {
    let mut f = EF::zero_vec(config.dense_size());
    for (claim, &alpha) in claims.iter().zip(alphas) {
        let st = config.sub_tables[claim.sub_table_id];
        let base = config.cumulative_areas[claim.sub_table_id];
        let width = 1usize << st.log_width;
        let z_row_eq = eval_eq::<EF>(&claim.z_row);
        let z_col_point = usize_to_point(claim.col_in_sub_table, st.log_width);
        let z_col_eq = eval_eq::<EF>(&z_col_point);
        // Outer product: f[base + r*width + c] += alpha * z_row_eq[r] * z_col_eq[c]
        f[base..base + st.area()]
            .par_chunks_mut(width)
            .enumerate()
            .for_each(|(r, chunk)| {
                let row_factor = alpha * z_row_eq[r];
                for (c, slot) in chunk.iter_mut().enumerate() {
                    *slot += row_factor * z_col_eq[c];
                }
            });
    }
    f
}
