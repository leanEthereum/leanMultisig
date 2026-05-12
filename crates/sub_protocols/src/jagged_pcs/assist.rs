//! Jagged-PCS "assist" sub-protocol (Lemma 2 of `jagged_pcs.tex`).
//!
//! Goal: replace the per-claim BP evaluations in the verifier's `F(i*)`
//! computation with O(K*m) cheap arithmetic + ONE BP evaluation per
//! (sub_table_id, is_next) group, at the cost of a small sumcheck the
//! prover runs after WHIR's folding completes.
//!
//! For each group `g` of claims sharing `(z_row_g, log_width_g, t_prev_g,
//! t_next_g)`, the per-claim BP eval differs only in `z_col`. Define
//! `h_g(z_col) = bp(z_row_g, z_col, i_star, t_prev_g, t_next_g)` -- this
//! is a multilinear polynomial in `z_col` (length `log_width_g`).
//!
//! Group contribution to `F(i*)`:
//!   `target_g = sum_{j in g} alpha_j * h_g(z_col_j)`.
//!
//! Apply Lemma 2 with `h = h_g`, `m = log_width_g`, `r = alpha`, reducing
//! `K_g` BP evals to one. The protocol per group:
//!
//! 1. Prover sends `target_g`.
//! 2. Run `log_width_g`-round sumcheck on
//!    `sum_b h_g(b) * sum_j alpha_j * eq(b, z_col_j) = target_g`.
//! 3. Verifier samples `rho_g` from the sumcheck and computes
//!    `eq_combined_g = sum_j alpha_j * eq(rho_g, z_col_j)`.
//! 4. Verifier checks `final_check == h_g(rho_g) * eq_combined_g` via
//!    ONE BP eval at `(z_row_g, rho_g, i_star, t_prev_g, t_next_g)`.
//!
//! The total contribution is `F(i*) = sum_g target_g`.

use std::collections::BTreeMap;

use backend::*;
use lean_vm::EF;

use super::branching::BranchingProgram;
use super::config::{JaggedConfig, usize_to_point};
use super::prover::JaggedClaim;

/// Group claims by `(sub_table_id, is_next, z_row)`. Within a group, all
/// claims share `z_row` and `t_prev/t_next` (modulo the is_next shift)
/// AND log_width; they differ in `col_in_sub_table`. Groups appear in
/// the order claims appear in the input (consecutive grouping).
fn group_indices(claims: &[JaggedClaim]) -> Vec<Vec<usize>> {
    let mut groups: Vec<Vec<usize>> = Vec::new();
    for (i, c) in claims.iter().enumerate() {
        let matches_last = groups
            .last()
            .map(|g| {
                let lead = &claims[g[0]];
                lead.sub_table_id == c.sub_table_id && lead.is_next == c.is_next && lead.z_row.0 == c.z_row.0
            })
            .unwrap_or(false);
        if matches_last {
            groups.last_mut().unwrap().push(i);
        } else {
            groups.push(vec![i]);
        }
    }
    groups
}

/// Evaluate `eq(rho, x)` where both points have length `n`.
fn eq_eval<F: Field>(rho: &[F], x: &[F]) -> F {
    assert_eq!(rho.len(), x.len());
    let mut out = F::ONE;
    for (a, b) in rho.iter().zip(x) {
        // eq_1(a, b) = a*b + (1-a)*(1-b) = 1 - a - b + 2*a*b
        let ab = *a * *b;
        out *= F::ONE - *a - *b + ab + ab;
    }
    out
}

/// Build the per-group `h_g(b) = bp(z_row_g, b, i_star, t_prev_g, t_next_g)`
/// closure. Returns evaluations at any `b` ∈ F^{log_width}.
fn h_g_eval(
    z_row: &[EF],
    z_col: &[EF],
    z_index: &[EF],
    t_prev: &[EF],
    t_next: &[EF],
    log_width: usize,
    log_dense_size: usize,
) -> EF {
    let bp = BranchingProgram {
        z_row,
        z_col,
        z_index,
        log_width,
        log_dense_size,
    };
    bp.eval(t_prev, t_next)
}

/// Encode `col` as the big-endian boolean point of length `log_width`,
/// returning a `Vec<EF>` (each entry is `EF::ZERO` or `EF::ONE`).
fn col_to_point(col: usize, log_width: usize) -> Vec<EF> {
    usize_to_point(col, log_width).0
}

// =============================================================================
// Prover
// =============================================================================

/// Run the assist sub-protocol on the prover side.
///
/// `i_star` is WHIR's final folding randomness. The prover writes one
/// `target_g` followed by `log_width_g` sumcheck polynomials per group.
pub fn jagged_assist_prove<P: FSProver<EF>>(
    config: &JaggedConfig,
    claims: &[JaggedClaim],
    alphas: &[EF],
    i_star: &MultilinearPoint<EF>,
    prover_state: &mut P,
) {
    // Lift cumulative-area bit vectors to EF representation once.
    let m = config.log_dense_size;
    let cumulative_area_bits_ef: Vec<Vec<EF>> = config
        .cumulative_areas
        .iter()
        .map(|&t| {
            (0..m)
                .rev()
                .map(|i| if (t >> i) & 1 == 1 { EF::ONE } else { EF::ZERO })
                .collect()
        })
        .collect();

    let groups = group_indices(claims);
    for indices in &groups {
        let lead = &claims[indices[0]];
        let st_id = lead.sub_table_id;
        let is_next = lead.is_next;
        let st = config.sub_tables[st_id];
        let log_width = st.log_width;
        // z_row is shared across all claims in this group (group key).
        let z_row = &lead.z_row.0;
        // t_prev for is_next is t_prev + 2^log_width (interpreted as integer).
        let t_prev_int = if is_next {
            config.cumulative_areas[st_id] + (1usize << log_width)
        } else {
            config.cumulative_areas[st_id]
        };
        let t_prev_ef: Vec<EF> = (0..m)
            .rev()
            .map(|i| if (t_prev_int >> i) & 1 == 1 { EF::ONE } else { EF::ZERO })
            .collect();
        let t_next_ef = &cumulative_area_bits_ef[st_id + 1];

        // Per-claim z_col points and alphas.
        let xs: Vec<Vec<EF>> = indices
            .iter()
            .map(|&j| col_to_point(claims[j].col_in_sub_table, log_width))
            .collect();
        let rs: Vec<EF> = indices.iter().map(|&j| alphas[j]).collect();

        // Compute target_g = sum_j r_j * h_g(x_j) by evaluating bp once
        // per claim. This is the same K BP evals the verifier USED to do;
        // here it's prover-only and we use it to seed the sumcheck.
        let mut target_g = EF::ZERO;
        for (x, r) in xs.iter().zip(&rs) {
            let bp_val = h_g_eval(z_row, x, &i_star.0, &t_prev_ef, t_next_ef, log_width, m);
            target_g += *r * bp_val;
        }
        prover_state.add_extension_scalar(target_g);

        // Sumcheck on sum_b P_g(b) = target_g, where
        //   P_g(b) = h_g(b) * sum_j r_j * eq(b, x_j).
        // P_g is a product of two multilinears in b, hence degree-2 per round.
        // We use the standard generic sumcheck (Lemma 1) -- prover sends a
        // degree-2 polynomial each round and the verifier samples a
        // challenge. m_g = log_width rounds.
        if log_width == 0 {
            // No sumcheck rounds; target_g already encodes the single term.
            continue;
        }

        // We'll run sumcheck variable-by-variable. At round j, the prover
        // has already fixed `rho_prefix` for the first j-1 variables and
        // sends a degree-2 polynomial P_j(X) = sum_{b in {0,1}^{m-j}}
        // P_g(rho_prefix, X, b).
        let mut rho_prefix: Vec<EF> = Vec::with_capacity(log_width);
        let mut current_claim_sum = target_g;
        for j in 0..log_width {
            // Compute P_j(X) at 3 distinct points: X = 0, X = 1, X = 2.
            // P_j(0) + P_j(1) must equal current_claim_sum.
            let mut p_at_0 = EF::ZERO;
            let mut p_at_2 = EF::ZERO;
            for (x, r) in xs.iter().zip(&rs) {
                // eq(rho_prefix, x[..j])
                let eq_prefix = eq_eval(&rho_prefix, &x[..j]);
                // For each lambda in {0, 2}, evaluate the inner sum.
                // We avoid lambda=1 since P_j(1) = current_claim_sum - P_j(0).
                for &lambda in &[EF::ZERO, EF::from_u32(2)] {
                    // eq(lambda, x[j]) -- since x[j] is in {0,1}, this is
                    // (1 - lambda) if x[j] == 0 else lambda.
                    let eq_at_lambda = if x[j] == EF::ZERO { EF::ONE - lambda } else { lambda };
                    // sum_b h_g(rho_prefix, lambda, b) * eq(b, x[j+1..]).
                    // Since x[j+1..] is on the cube, this is just
                    // h_g(rho_prefix, lambda, x[j+1..]).
                    let mut sub_z_col: Vec<EF> = Vec::with_capacity(log_width);
                    sub_z_col.extend_from_slice(&rho_prefix);
                    sub_z_col.push(lambda);
                    sub_z_col.extend_from_slice(&x[j + 1..]);
                    let h_val = h_g_eval(z_row, &sub_z_col, &i_star.0, &t_prev_ef, t_next_ef, log_width, m);
                    let term = *r * eq_prefix * eq_at_lambda * h_val;
                    if lambda == EF::ZERO {
                        p_at_0 += term;
                    } else {
                        p_at_2 += term;
                    }
                }
            }
            let p_at_1 = current_claim_sum - p_at_0;
            // Send the polynomial via 3 EF scalars at X = 0, 1, 2 (the
            // standard 3-point representation for a degree-2 univariate).
            // Verifier reconstructs the polynomial via interpolation.
            prover_state.add_extension_scalars(&[p_at_0, p_at_1, p_at_2]);

            // Sample the next challenge.
            let rho_j: EF = prover_state.sample();
            rho_prefix.push(rho_j);
            // Update the claimed sum to P_j(rho_j).
            current_claim_sum = polynomial_eval_degree2_via_3_points(p_at_0, p_at_1, p_at_2, rho_j);
        }
        let _ = current_claim_sum; // unused on prover side; verifier will recompute and check.
    }
}

/// Evaluate a degree-2 polynomial given by its values at `X = 0, 1, 2` at
/// arbitrary `x ∈ F`. Standard Lagrange interpolation over `{0, 1, 2}`.
fn polynomial_eval_degree2_via_3_points(p0: EF, p1: EF, p2: EF, x: EF) -> EF {
    // L_0(x) = (x-1)(x-2)/2; L_1(x) = -(x-0)(x-2); L_2(x) = (x-0)(x-1)/2.
    let x_minus_1 = x - EF::ONE;
    let x_minus_2 = x - EF::from_u32(2);
    let half = EF::from_u32(2).inverse();
    let l0 = x_minus_1 * x_minus_2 * half;
    let l1 = -x * x_minus_2;
    let l2 = x * x_minus_1 * half;
    p0 * l0 + p1 * l1 + p2 * l2
}

// =============================================================================
// Verifier
// =============================================================================

/// Verify the assist sub-protocol and return `F(i*) = sum_g target_g`.
#[allow(clippy::too_many_arguments)]
pub fn jagged_assist_verify<V: FSVerifier<EF>>(
    config: &JaggedConfig,
    claims: &[JaggedClaim],
    alphas: &[EF],
    cumulative_area_bits_ef: &[Vec<EF>],
    shifted_t_prev_cache: &BTreeMap<usize, Vec<EF>>,
    i_star: &MultilinearPoint<EF>,
    m: usize,
    verifier_state: &mut V,
) -> ProofResult<EF> {
    let groups = group_indices(claims);
    let mut f_at_istar = EF::ZERO;
    for indices in &groups {
        let lead = &claims[indices[0]];
        let st_id = lead.sub_table_id;
        let is_next = lead.is_next;
        let st = config.sub_tables[st_id];
        let log_width = st.log_width;
        let z_row = &lead.z_row.0;
        let t_prev_ef: &[EF] = if is_next {
            shifted_t_prev_cache.get(&st_id).unwrap()
        } else {
            &cumulative_area_bits_ef[st_id]
        };
        let t_next_ef = &cumulative_area_bits_ef[st_id + 1];

        let xs: Vec<Vec<EF>> = indices
            .iter()
            .map(|&j| col_to_point(claims[j].col_in_sub_table, log_width))
            .collect();
        let rs: Vec<EF> = indices.iter().map(|&j| alphas[j]).collect();

        let target_g: EF = verifier_state.sample_next_extension_scalar()?;

        if log_width == 0 {
            // No sumcheck; target_g must equal r_0 * h_g(()), which we
            // verify by evaluating bp once.
            assert_eq!(indices.len(), 1, "log_width=0 implies a single-column sub-table");
            let bp_val = h_g_eval(z_row, &[], &i_star.0, t_prev_ef, t_next_ef, log_width, m);
            if rs[0] * bp_val != target_g {
                return Err(ProofError::InvalidProof);
            }
            f_at_istar += target_g;
            continue;
        }

        let mut rho_prefix: Vec<EF> = Vec::with_capacity(log_width);
        let mut current_claim_sum = target_g;
        for _j in 0..log_width {
            let poly = verifier_state.next_extension_scalars_vec(3)?;
            let p_at_0 = poly[0];
            let p_at_1 = poly[1];
            let p_at_2 = poly[2];
            if p_at_0 + p_at_1 != current_claim_sum {
                return Err(ProofError::InvalidProof);
            }
            let rho_j: EF = verifier_state.sample();
            rho_prefix.push(rho_j);
            current_claim_sum = polynomial_eval_degree2_via_3_points(p_at_0, p_at_1, p_at_2, rho_j);
        }

        // Final check: claimed_sum_after_sumcheck == h_g(rho) * sum_j r_j * eq(rho, x_j).
        let mut eq_combined = EF::ZERO;
        for (x, r) in xs.iter().zip(&rs) {
            eq_combined += *r * eq_eval(&rho_prefix, x);
        }
        let h_at_rho = h_g_eval(z_row, &rho_prefix, &i_star.0, t_prev_ef, t_next_ef, log_width, m);
        if h_at_rho * eq_combined != current_claim_sum {
            return Err(ProofError::InvalidProof);
        }

        f_at_istar += target_g;
    }
    Ok(f_at_istar)
}

// Helper trait extension: pull a single EF scalar from the verifier
// state. The trait already has `next_extension_scalars_vec`; we use it
// here for a single scalar.
trait FSVerifierSingle<EF>: FSVerifier<EF>
where
    EF: ExtensionField<PF<EF>>,
{
    fn sample_next_extension_scalar(&mut self) -> ProofResult<EF> {
        Ok(self.next_extension_scalars_vec(1)?[0])
    }
}
impl<EF: ExtensionField<PF<EF>>, V: FSVerifier<EF>> FSVerifierSingle<EF> for V {}
