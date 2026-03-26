use backend::*;
use lean_vm::{EF, F};
use tracing::{info_span, instrument};

use crate::*;

/*
Details: https://github.com/TomWambsgans/misc/blob/master/pcs_in_2_sumchecks.pdf
*/

#[instrument(skip_all, fields(n_claims = statements.len(), n_vars = statements[0].total_num_variables))]
pub fn prove_reduction_many_sparse_claims_to_single_dense(
    prover_state: &mut impl FSProver<EF>,
    statements: &[SparseStatement<EF>],
    polynomial: &MleOwned<EF>,
) -> Evaluation<EF> {
    let l = statements[0].total_num_variables;
    assert!(l >= 2);
    assert!(statements.iter().all(|s| s.total_num_variables == l));

    let gamma: EF = prover_state.sample();
    let y_alpha = claimed_sum(statements, gamma);
    let f = polynomial.as_base().unwrap();
    let l0 = l - l / 2; // number of SVO rounds = ceil(l/2)
    let n_lo = 1usize << (l / 2);
    let n_hi = 1usize << l0;

    // --- Precompute per-claim data ---
    // For each claim i: eq_svo_i = eval_eq(w_i^hi), A_i[k] = sum_{b^lo} eq_lo_i[b^lo] * f(b^lo, k)
    // Claims within a statement that share eq_svo are merged (accumulators summed with gamma weights).
    let (mut eq_svos, mut accumulators, weight_info) =
        info_span!("precompute").in_scope(|| precompute(statements, gamma, l, f, n_lo, n_hi));

    // --- SVO rounds: fold X_l, X_{l-1}, ..., X_{l/2+1} (right-to-left = LSB first) ---
    let mut challenges = Vec::with_capacity(l0);
    let mut sum = y_alpha;

    for _round in 0..l0 {
        let mut c0 = EF::ZERO;
        let mut c2 = EF::ZERO;
        for (eq, acc) in eq_svos.iter().zip(&accumulators) {
            let half = acc.len() / 2;
            for j in 0..half {
                c0 += eq[2 * j] * acc[2 * j];
                c2 += (eq[2 * j + 1] - eq[2 * j]) * (acc[2 * j + 1] - acc[2 * j]);
            }
        }
        let c1 = sum - c0 - c0 - c2;
        let poly = DensePolynomial::new(vec![c0, c1, c2]);
        prover_state.add_sumcheck_polynomial(&poly.coeffs, None);
        let r: EF = prover_state.sample();
        challenges.push(r);
        sum = poly.evaluate(r);
        for (eq, acc) in eq_svos.iter_mut().zip(accumulators.iter_mut()) {
            fold_lsb(eq, r);
            fold_lsb(acc, r);
        }
    }

    // --- Post-SVO: fold f and build remaining weight for lo-half product sumcheck ---
    let (mut f_folded, mut w_rest) = info_span!("post_svo").in_scope(|| {
        // Multi-fold f at SVO challenges (right-to-left = fold LSBs)
        let mut r_rev = challenges.clone();
        r_rev.reverse();
        let eq_at_r = eval_eq(&r_rev);
        let mut f_folded = EF::zero_vec(n_lo);
        f_folded.par_chunks_mut(64).enumerate().for_each(|(ci, chunk)| {
            for (k, dest) in chunk.iter_mut().enumerate() {
                let j = ci * 64 + k;
                *dest = dot_product(eq_at_r.iter().copied(), f[j * n_hi..][..n_hi].iter().copied());
            }
        });

        // Weight: w_rest[b^lo] = sum_claims eq_svo_scalar * gamma * eq_lo_ns[sparse_offset + b^lo_ns]
        let mut w_rest = EF::zero_vec(n_lo);
        for (eq_svo, (eq_lo, vals)) in eq_svos.iter().zip(&weight_info) {
            let svo_scalar = eq_svo[0]; // fully folded to 1 entry
            let n_ns = eq_lo.len();
            for &(gp, sel_lo) in vals {
                let scale = gp * svo_scalar;
                let off = sel_lo * n_ns;
                for (b, &v) in eq_lo.iter().enumerate() {
                    w_rest[off + b] += scale * v;
                }
            }
        }
        (f_folded, w_rest)
    });

    // --- Remaining lo-half sumcheck via standard product sumcheck (right-to-left via bit-reverse) ---
    bit_reverse_permutation(&mut f_folded);
    bit_reverse_permutation(&mut w_rest);
    let f_mle = MleOwned::Extension(f_folded);
    let w_mle = MleOwned::Extension(w_rest);
    let f_p = f_mle.pack();
    let w_p = w_mle.pack();
    let (rest_r, _, folded, _) = run_product_sumcheck(&f_p.by_ref(), &w_p.by_ref(), prover_state, sum, l / 2, 0);

    let p_eval = folded.evaluate(&MultilinearPoint(vec![]));
    let mut all_r: Vec<EF> = challenges;
    all_r.extend(rest_r.0);
    all_r.reverse();
    Evaluation::new(all_r, p_eval)
}

/// Precomputes eq_svo tables, accumulators, and weight metadata for all claims.
/// Returns parallel arrays: one entry per "merged claim group" (= per SparseStatement
/// when all selector bits fit in the lo-half, otherwise per SparseValue).
fn precompute(
    statements: &[SparseStatement<EF>],
    gamma: EF,
    l: usize,
    f: &[F],
    _n_lo: usize,
    n_hi: usize,
) -> (
    Vec<Vec<EF>>,                     // eq_svos
    Vec<Vec<EF>>,                     // accumulators
    Vec<(Vec<EF>, Vec<(EF, usize)>)>, // (eq_lo, per-value (gamma_pow, sel_lo))
) {
    let half = l / 2;
    let mut starts = Vec::with_capacity(statements.len());
    let mut offset = 0;
    for smt in statements {
        starts.push(offset);
        offset += smt.values.len();
    }
    let gamma_pows: Vec<EF> = gamma.powers().collect_n(offset);

    // Each statement produces one or more (eq_svo, accumulator, weight_info) entries.
    let groups: Vec<Vec<(Vec<EF>, Vec<EF>, (Vec<EF>, Vec<(EF, usize)>))>> = statements
        .par_iter()
        .enumerate()
        .map(|(si, smt)| {
            let vi = starts[si];
            let s = smt.selector_num_variables();
            let s_lo = s.min(half);
            let s_hi = s - s_lo;
            let lo_ns = half - s_lo; // "lo non-sparse" = the number of non-sparse (extension field) variables in the lo-half part
            let eq_lo = if lo_ns > 0 {
                eval_eq(&smt.point[..lo_ns])
            } else {
                vec![EF::ONE]
            };
            let n_ns = eq_lo.len();

            let accum = |acc: &mut [EF], e: &SparseValue<EF>, gp: EF| {
                let sel_lo = if s_hi > 0 { e.selector >> s_hi } else { e.selector };
                let base = sel_lo * n_ns;
                for (b, &eq_v) in eq_lo.iter().enumerate() {
                    let coeff = gp * eq_v;
                    for (a, &fv) in acc.iter_mut().zip(&f[(base + b) * n_hi..][..n_hi]) {
                        *a += coeff * fv;
                    }
                }
            };

            if s_hi == 0 {
                // All selector bits in lo-half → shared eq_svo → merge
                let eq_svo = eval_eq(&smt.point[lo_ns..]);
                let mut acc = EF::zero_vec(n_hi);
                let mut vals = Vec::with_capacity(smt.values.len());
                for (i, e) in smt.values.iter().enumerate() {
                    accum(&mut acc, e, gamma_pows[vi + i]);
                    vals.push((gamma_pows[vi + i], e.selector));
                }
                vec![(eq_svo, acc, (eq_lo, vals))]
            } else {
                // Selector bits spill into hi-half → per-value entries
                smt.values
                    .iter()
                    .enumerate()
                    .map(|(i, e)| {
                        let gp = gamma_pows[vi + i];
                        let sel_lo = e.selector >> s_hi;
                        let sel_hi = e.selector & ((1 << s_hi) - 1);
                        let mut eq_svo = EF::zero_vec(n_hi);
                        compute_sparse_eval_eq(sel_hi, &smt.point[lo_ns..], &mut eq_svo, EF::ONE);
                        let mut acc = EF::zero_vec(n_hi);
                        accum(&mut acc, e, gp);
                        (eq_svo, acc, (eq_lo.clone(), vec![(gp, sel_lo)]))
                    })
                    .collect()
            }
        })
        .collect();

    let mut eq_svos = Vec::new();
    let mut accumulators = Vec::new();
    let mut weight_info = Vec::new();
    for group in groups {
        for (eq, acc, wi) in group {
            eq_svos.push(eq);
            accumulators.push(acc);
            weight_info.push(wi);
        }
    }
    (eq_svos, accumulators, weight_info)
}

pub fn verify_reduction_many_sparse_claims_to_single_dense(
    verifier_state: &mut impl FSVerifier<EF>,
    statements: &[SparseStatement<EF>],
) -> Result<Evaluation<EF>, ProofError> {
    let l = statements[0].total_num_variables;
    assert!(statements.iter().all(|s| s.total_num_variables == l));

    let gamma: EF = verifier_state.sample();
    let y_alpha = claimed_sum(statements, gamma);
    let Evaluation {
        point: r,
        value: final_sum,
    } = sumcheck_verify(verifier_state, l, 2, y_alpha, None)?;
    let point = r.reversed();
    let w_eval = eval_weight_at_point(statements, gamma, &point);
    Ok(Evaluation::new(point, final_sum / w_eval))
}

// ---------------------------------------------------------------------------

fn claimed_sum(statements: &[SparseStatement<EF>], gamma: EF) -> EF {
    let mut sum = EF::ZERO;
    let mut gp = EF::ONE;
    for smt in statements {
        for e in &smt.values {
            sum += gp * e.value;
            gp *= gamma;
        }
    }
    sum
}

#[inline]
fn fold_lsb(v: &mut Vec<EF>, r: EF) {
    let half = v.len() / 2;
    for i in 0..half {
        v[i] = v[2 * i] + r * (v[2 * i + 1] - v[2 * i]);
    }
    v.truncate(half);
}

fn eval_weight_at_point(statements: &[SparseStatement<EF>], gamma: EF, point: &MultilinearPoint<EF>) -> EF {
    let mut value = EF::ZERO;
    let mut gp = EF::ONE;
    for smt in statements {
        let inner_eq = smt.point.eq_poly_outside(&MultilinearPoint(
            point[point.len() - smt.inner_num_variables()..].to_vec(),
        ));
        let s = smt.selector_num_variables();
        for e in &smt.values {
            let sel_eq: EF = (0..s)
                .map(|j| {
                    if e.selector & (1 << (s - 1 - j)) == 0 {
                        EF::ONE - point[j]
                    } else {
                        point[j]
                    }
                })
                .product();
            value += gp * sel_eq * inner_eq;
            gp *= gamma;
        }
    }
    value
}
