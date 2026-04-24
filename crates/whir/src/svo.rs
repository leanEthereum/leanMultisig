#![allow(clippy::needless_range_loop)]
// SVO + split-eq precompute for the first `l_0` WHIR sumcheck rounds.
//
// Implements the pipeline described in `misc/whir_sumcheck.tex`:
//   (1) `compress_eq_claim` / `compress_next_claim_bucketed` -> `CompressedGroup`s
//   (2) `build_accumulators` -> per-round `AccGroup` (size `3^r` ternary slabs)
//   (3) `round_message` -> `(c0, c2)` from accumulators + Lagrange weights
//
// Under our fold-from-the-right (LSB-fold) convention:
//   - round 0 folds `X_l` (the LSB of the big-endian index), sampling `rho_0`;
//   - round `r` folds `X_{l-r}`, sampling `rho_r`;
//   - `bsvo = (bsvo_1, .., bsvo_{l_0})` covers the last `l_0` coords (big-endian),
//     so `bsvo_{l_0 - r}` is active at round `r`.
//
// Accumulator feed uses NATURAL big-endian: at round `r`, `Q_r` and `E_r` are
// indexed over `(bsvo_{r_F+1}, .., bsvo_{l_0})` (big-endian), which places
// the active coord at input position 0 -> output stride `3^0` = innermost
// ternary digit after `grid_expand`. Slabs are `3j` (active=0) and `3j+2`
// (active=2). Lagrange weights are built from challenges in natural order
// `(rho_0, rho_1, .., rho_{r-1})`.

use field::{ExtensionField, Field};
use poly::{PARALLEL_THRESHOLD, PF, compute_eval_eq, eval_eq};
use rayon::prelude::*;

/// One `(eq(bsvo, w_svo), p_bar(bsvo))` sub-group consumed by
/// `build_accumulators`. `w_svo` has length `l_0`; `p_bar` has length `2^l_0`
/// in `EF`. Index layout of `p_bar` is big-endian over `bsvo` (coord 1 is MSB).
#[derive(Debug, Clone)]
pub(crate) struct CompressedGroup<EF> {
    pub(crate) w_svo: Vec<EF>,
    pub(crate) p_bar: Vec<EF>,
}

/// Per-group, per-round accumulators. `acc_a[r][j]`, `acc_c[r][j]`,
/// `acc_b[r][j]` hold `tildeQ * tildeE` at active-coord values 0, 1, 2
/// respectively, summed with Lagrange weights to produce `h(0), h(1), h(2)`
/// of the round polynomial. Total size per group: `sum_r 3 * 3^r = (3^{l_0+1} - 3)/2`.
#[derive(Debug)]
pub(crate) struct AccGroup<EF> {
    pub(crate) acc_a: Vec<Vec<EF>>,
    pub(crate) acc_c: Vec<Vec<EF>>,
    pub(crate) acc_b: Vec<Vec<EF>>,
}

/// Same as [`grid_expand`] but writes into `out`, using `scratch` as the swap
/// buffer. Both buffers are resized in place; callers can keep them across
/// calls to amortize allocation.
pub(crate) fn grid_expand_into<EF: Field>(f: &[EF], l: usize, out: &mut Vec<EF>, scratch: &mut Vec<EF>) {
    assert_eq!(f.len(), 1 << l, "grid_expand_into: f.len() must be 2^l");
    let out_len = 3_usize.pow(l as u32);
    if l == 0 {
        out.clear();
        out.extend_from_slice(f);
        return;
    }
    // Pick parity so the final stage lands in `out`.
    let (mut cur, mut nxt): (&mut Vec<EF>, &mut Vec<EF>) = if l.is_multiple_of(2) {
        (out, scratch)
    } else {
        (scratch, out)
    };
    cur.clear();
    cur.extend_from_slice(f);
    cur.resize(out_len, EF::ZERO);
    nxt.clear();
    nxt.resize(out_len, EF::ZERO);
    for stage in 0..l {
        let s = 3_usize.pow(stage as u32);
        let block_count = 1usize << (l - stage - 1);
        let in_total = block_count * 2 * s;
        let out_total = block_count * 3 * s;
        let cur_slice = &cur[..in_total];
        let next_slice = &mut nxt[..out_total];
        let block_kernel = |(in_block, out_block): (&[EF], &mut [EF])| {
            let (lo, hi) = in_block.split_at(s);
            for j in 0..s {
                let f0 = lo[j];
                let f1 = hi[j];
                out_block[3 * j] = f0;
                out_block[3 * j + 1] = f1;
                out_block[3 * j + 2] = f1.double() - f0;
            }
        };
        if out_total < PARALLEL_THRESHOLD {
            for pair in cur_slice.chunks_exact(2 * s).zip(next_slice.chunks_exact_mut(3 * s)) {
                block_kernel(pair);
            }
        } else {
            cur_slice
                .par_chunks_exact(2 * s)
                .zip(next_slice.par_chunks_exact_mut(3 * s))
                .for_each(block_kernel);
        }
        std::mem::swap(&mut cur, &mut nxt);
    }
    debug_assert_eq!(cur.len(), out_len);
}

/// Extend a `3^r`-size Lagrange tensor to `3^{r+1}` in place by tensoring with
/// `(L_0, L_1, L_2)` at `c`, where `L_0(c) = (c-1)(c-2)/2`, `L_1(c) = c(2-c)`,
/// `L_2(c) = c(c-1)/2`.
pub(crate) fn lagrange_tensor_extend<EF: Field>(out: &mut Vec<EF>, c: EF) {
    let inv_two = EF::TWO.inverse();
    let two = EF::TWO;
    let c_m1 = c - EF::ONE;
    let c_m2 = c - two;
    let l0 = c_m1 * c_m2 * inv_two;
    let l1 = c * (two - c);
    let l2 = c * c_m1 * inv_two;
    let old_len = out.len();
    out.resize(old_len * 3, EF::ZERO);
    // Walk backwards so writes never overlap unread input.
    for i in (0..old_len).rev() {
        let v = out[i];
        out[3 * i] = v * l0;
        out[3 * i + 1] = v * l1;
        out[3 * i + 2] = v * l2;
    }
}

// =========================================================================
// Row-reduction kernels shared by the eq-claim and next-claim compressors.
// =========================================================================

/// Compute `acc[bsvo] = Σ_b coef[b] * rows[sel_offset + b*svo_len + bsvo]`.
/// Serial or parallel over `b` depending on `e_len * svo_len`.
fn reduce_svo_rows_one<EF>(rows: &[PF<EF>], coef: &[EF], sel_offset: usize, svo_len: usize) -> Vec<EF>
where
    EF: ExtensionField<PF<EF>>,
{
    let e_len = coef.len();
    let zero = || EF::zero_vec(svo_len);
    let step = |mut acc: Vec<EF>, b: usize| {
        let e = coef[b];
        let row = &rows[sel_offset + b * svo_len..][..svo_len];
        for bsvo in 0..svo_len {
            acc[bsvo] += e * row[bsvo];
        }
        acc
    };
    let merge = |mut a: Vec<EF>, b: Vec<EF>| {
        for (x, y) in a.iter_mut().zip(&b) {
            *x += *y;
        }
        a
    };
    if e_len * svo_len < PARALLEL_THRESHOLD {
        (0..e_len).fold(zero(), step)
    } else {
        (0..e_len).into_par_iter().fold(zero, step).reduce(zero, merge)
    }
}

/// Same shape as [`reduce_svo_rows_one`] but accumulates two coefficient tables
/// in one pass (reads each `rows` entry once).
fn reduce_svo_rows_two<EF>(
    rows: &[PF<EF>],
    coef_a: &[EF],
    coef_b: &[EF],
    sel_offset: usize,
    svo_len: usize,
) -> (Vec<EF>, Vec<EF>)
where
    EF: ExtensionField<PF<EF>>,
{
    let e_len = coef_a.len();
    debug_assert_eq!(coef_b.len(), e_len);
    let zero = || (EF::zero_vec(svo_len), EF::zero_vec(svo_len));
    let step = |(mut a, mut b): (Vec<EF>, Vec<EF>), idx: usize| {
        let ca = coef_a[idx];
        let cb = coef_b[idx];
        let row = &rows[sel_offset + idx * svo_len..][..svo_len];
        for bsvo in 0..svo_len {
            let v = row[bsvo];
            a[bsvo] += ca * v;
            b[bsvo] += cb * v;
        }
        (a, b)
    };
    let merge = |(mut ax, mut bx): (Vec<EF>, Vec<EF>), (ay, by): (Vec<EF>, Vec<EF>)| {
        for (x, y) in ax.iter_mut().zip(&ay) {
            *x += *y;
        }
        for (x, y) in bx.iter_mut().zip(&by) {
            *x += *y;
        }
        (ax, bx)
    };
    if e_len * svo_len < PARALLEL_THRESHOLD {
        (0..e_len).fold(zero(), step)
    } else {
        (0..e_len).into_par_iter().fold(zero, step).reduce(zero, merge)
    }
}

// =========================================================================
// eq-claim compression (Algorithm 1 "alg:compress_sparse" + merge).
// =========================================================================

/// One `CompressedGroup` per eq-claim group. Requires the non-spill regime
/// (`s <= l - l_0`) — eq spills are absorbed into the point upstream by
/// [`relax_eq_spill_statements`] before reaching this function.
/// Merges all `K` selectors via the shared `E_split` table (Algorithm 2 "alg:merge").
///
/// `p_bar[bsvo] = Σ_j alpha_j * Σ_{b' ∈ {0,1}^{l - l_0 - s}} eq(b', p_split) * f(sel_j, b', bsvo)`
/// where `p_split = p[0..m - l_0]` and `p_svo = p[m - l_0..m]`.
pub(crate) fn compress_eq_claim<EF>(
    f: &[PF<EF>],
    sel_bits: &[usize],
    inner_point: &[EF],
    alpha_powers: &[EF],
    l: usize,
    l_0: usize,
    s: usize,
) -> CompressedGroup<EF>
where
    EF: ExtensionField<PF<EF>>,
{
    assert_eq!(sel_bits.len(), alpha_powers.len());
    assert_eq!(inner_point.len(), l - s);
    assert!(s + l_0 <= l, "compress_eq_claim non-spill requires s <= l - l_0");
    let m_split = l - l_0 - s;
    let p_split = &inner_point[..m_split];
    let p_svo = &inner_point[m_split..];

    let e_split = eval_eq(p_split); // length 2^{m_split}; correct for m_split == 0 too
    let svo_len = 1usize << l_0;
    let mut p_bar = vec![EF::ZERO; svo_len];

    for (&sel_j, &alpha_j) in sel_bits.iter().zip(alpha_powers.iter()) {
        let sel_offset = sel_j << (l - s);
        let contrib = reduce_svo_rows_one::<EF>(f, &e_split, sel_offset, svo_len);
        for (p, s) in p_bar.iter_mut().zip(contrib.iter()) {
            *p += alpha_j * *s;
        }
    }

    CompressedGroup {
        w_svo: p_svo.to_vec(),
        p_bar,
    }
}

// =========================================================================
// nxt-claim bucketed compression (Algorithm 4 "alg:next_bucketed").
// =========================================================================

/// For one nxt-claim group: `K` selectors sharing inner point `p ∈ Fq^m`.
/// Emits exactly `l_0 + 2` `CompressedGroup`s (one shared Σ_split, `l_0`
/// bucket-B sub-groups sharing `P_eq`, one bucket-C slice), with the per-claim
/// α-weighted sums over the group's selectors merged inside.
pub(crate) fn compress_next_claim_bucketed<EF>(
    f: &[PF<EF>],
    sel_bits: &[usize],
    inner_point: &[EF],
    alpha_powers: &[EF],
    l: usize,
    l_0: usize,
    s: usize,
) -> Vec<CompressedGroup<EF>>
where
    EF: ExtensionField<PF<EF>>,
{
    assert_eq!(sel_bits.len(), alpha_powers.len());
    let m = l - s;
    assert_eq!(inner_point.len(), m);
    assert!(s + l_0 <= l, "selector-inside-split requires s <= l - l_0");
    let m_split = m - l_0;
    let split_len = 1usize << m_split;
    let svo_len = 1usize << l_0;

    // Pure-Fq precompute (no f access).
    //   bar_T_split[β] = Σ_{J < m_split} c[J] * T_J^split(β).
    //   E_split[β] = eq(β, p[0..m_split]).
    //   c_omega = Π_{j<m} p[j] (returned from build_bar_t_split as suf[0]).
    //   c[J] = (Π_{j > J, j < m} p[j]) * (1 - p[J]).
    let (bar_t_split, c_omega) = build_bar_t_split(inner_point, m_split, m);
    let e_split = eval_eq(&inner_point[..m_split]);
    debug_assert_eq!(bar_t_split.len(), split_len);
    debug_assert_eq!(e_split.len(), split_len);

    let c_pivot: Vec<EF> = (m_split..m)
        .map(|j| {
            let tail: EF = inner_point[j + 1..].iter().copied().product();
            (EF::ONE - inner_point[j]) * tail
        })
        .collect();

    let mut sigma_split = vec![EF::ZERO; svo_len];
    let mut p_eq = vec![EF::ZERO; svo_len];
    let mut s_omega = vec![EF::ZERO; svo_len];

    for (&sel_j, &alpha_j) in sel_bits.iter().zip(alpha_powers.iter()) {
        let sel_offset = sel_j << (l - s);

        let (sig_contrib, eq_contrib) = reduce_svo_rows_two::<EF>(f, &bar_t_split, &e_split, sel_offset, svo_len);

        // Bucket-C slice read at β_split = 1^{m_split}.
        let c_base = sel_offset + ((split_len - 1) << l_0);
        for bsvo in 0..svo_len {
            s_omega[bsvo] += alpha_j * f[c_base + bsvo];
        }

        for bsvo in 0..svo_len {
            sigma_split[bsvo] += alpha_j * sig_contrib[bsvo];
            p_eq[bsvo] += alpha_j * eq_contrib[bsvo];
        }
    }

    // Emit sub-groups.
    let mut out: Vec<CompressedGroup<EF>> = Vec::with_capacity(l_0 + 2);
    // Bucket A: (wsvo = 0^{l_0}, p_bar = Σ_split).
    out.push(CompressedGroup {
        w_svo: vec![EF::ZERO; l_0],
        p_bar: sigma_split,
    });
    // Bucket B: one sub-group per pivot j in [m_split, m); pivot_pos = j - m_split ∈ [0, l_0).
    for (pivot_pos, &cp) in c_pivot.iter().enumerate() {
        // w layout: inner_point[m_split..m_split+pivot_pos] | ONE | 0..0.
        let mut w = vec![EF::ZERO; l_0];
        w[..pivot_pos].copy_from_slice(&inner_point[m_split..m_split + pivot_pos]);
        w[pivot_pos] = EF::ONE;
        let pb: Vec<EF> = p_eq.iter().map(|v| *v * cp).collect();
        out.push(CompressedGroup { w_svo: w, p_bar: pb });
    }
    // Bucket C: (wsvo = 1^{l_0}, p_bar = c_omega * S_omega).
    let mut pb = s_omega;
    for v in pb.iter_mut() {
        *v *= c_omega;
    }
    out.push(CompressedGroup {
        w_svo: vec![EF::ONE; l_0],
        p_bar: pb,
    });
    assert_eq!(out.len(), l_0 + 2);
    out
}

/// Build `bar_T_split[β] = Σ_{J < m_split} c[J] * T_J^split(β)` where
///   c[J] = (Π_{j>J, j<m} p[j]) * (1 - p[J])
///   T_J^split(β) = Π_{j<J} eq(p[j], β[j]) * β[J] * Π_{j>J, j<m_split} (1-β[j]).
///
/// For every β, exactly one pivot J contributes (the position of the last `1`
/// in β among coords `[0, m_split)`): all coords after J must be 0 to avoid
/// the `(1-β)` factor, and β[J] must be 1. So
///
///   bar_T[β] = c[J_last_1(β)] * Π_{j<J_last_1(β)} eq(p[j], β[j])    if β ≠ 0
///            = 0                                                     else.
///
/// Also returns `c_omega = Π_{j<m} p[j]` (= `suf[0]`) since the caller needs it.
fn build_bar_t_split<EF: Field>(p: &[EF], m_split: usize, m: usize) -> (Vec<EF>, EF) {
    let out_len = 1usize << m_split;
    let mut bar_t = vec![EF::ZERO; out_len];

    // Suffix products: suf[j] = Π_{j' ∈ [j, m)} p[j'], with suf[m] = 1.
    let mut suf = vec![EF::ONE; m + 1];
    for j in (0..m).rev() {
        suf[j] = suf[j + 1] * p[j];
    }
    // c[J] = suf[J+1] * (1 - p[J]). Fill bar_t with a single incremental pass
    // over growing prefix_eq tables (prefix = eval_eq(p[0..j])).
    let mut prefix = vec![EF::ONE];
    for j in 0..m_split {
        let c_j = suf[j + 1] * (EF::ONE - p[j]);
        let stride = 1usize << (m_split - j);
        let offset = 1usize << (m_split - 1 - j);
        let prefix_len = prefix.len();
        debug_assert_eq!(prefix_len, 1 << j);
        for k in 0..prefix_len {
            bar_t[k * stride + offset] = c_j * prefix[k];
        }
        if j + 1 < m_split {
            let p_j = p[j];
            let one_minus = EF::ONE - p_j;
            let mut new_prefix = Vec::with_capacity(2 * prefix_len);
            for &v in &prefix {
                new_prefix.push(v * one_minus);
                new_prefix.push(v * p_j);
            }
            prefix = new_prefix;
        }
    }
    (bar_t, suf[0])
}

// =========================================================================
// Per-round accumulators (Algorithm 5 "alg:accs").
// =========================================================================

/// For a single group, build `{acc_a[r], acc_c[r], acc_b[r]}` for `r = 0..l_0`,
/// each of length `3^r`. Pattern per round (using the NATURAL feed layout —
/// see module docstring):
///   Q_r = P_bar partially-evaluated on the first `r_F = l_0 - r - 1` coords
///         (big-endian: the LEADING coords of the bsvo array). Size 2^{r+1}.
///   E_r = eval_eq(w_svo[r_F..l_0])       size 2^{r+1}.
///   tilde_Q, tilde_E = grid_expand(..)   size 3^{r+1}.
///   acc_a[r][j] = tilde_Q[3j]   * tilde_E[3j]
///   acc_c[r][j] = tilde_Q[3j+1] * tilde_E[3j+1]
///   acc_b[r][j] = tilde_Q[3j+2] * tilde_E[3j+2]    for j in [0, 3^r).
pub(crate) fn build_accumulators_single<EF>(group: &CompressedGroup<EF>, l_0: usize) -> AccGroup<EF>
where
    EF: ExtensionField<PF<EF>>,
{
    assert_eq!(group.w_svo.len(), l_0);
    assert_eq!(group.p_bar.len(), 1 << l_0);

    let mut acc_a: Vec<Vec<EF>> = vec![Vec::new(); l_0];
    let mut acc_c: Vec<Vec<EF>> = vec![Vec::new(); l_0];
    let mut acc_b: Vec<Vec<EF>> = vec![Vec::new(); l_0];

    // Persistent scratch reused across rounds; `grid_expand_into` handles sizing.
    let cap = 3_usize.pow(l_0 as u32);
    let mut q: Vec<EF> = group.p_bar.clone();
    let mut tilde_q: Vec<EF> = Vec::with_capacity(cap);
    let mut tilde_e: Vec<EF> = Vec::with_capacity(cap);
    let mut scratch_q: Vec<EF> = Vec::with_capacity(cap);
    let mut scratch_e: Vec<EF> = Vec::with_capacity(cap);
    let mut e_buf: Vec<EF> = Vec::with_capacity(1 << l_0);
    for r_idx in 0..l_0 {
        let r = l_0 - 1 - r_idx;
        let r_f = l_0 - r - 1;
        let big_l = r + 1;
        debug_assert_eq!(q.len(), 1 << big_l);

        e_buf.clear();
        e_buf.resize(1 << big_l, EF::ZERO);
        compute_eval_eq::<PF<EF>, EF, false>(&group.w_svo[r_f..], &mut e_buf, EF::ONE);

        grid_expand_into(&q, big_l, &mut tilde_q, &mut scratch_q);
        grid_expand_into(&e_buf, big_l, &mut tilde_e, &mut scratch_e);

        let s = 3_usize.pow(r as u32);
        let mut a = EF::zero_vec(s);
        let mut c_mid = EF::zero_vec(s);
        let mut b = EF::zero_vec(s);
        let fill = |(j, (a_j, (c_j, b_j))): (usize, (&mut EF, (&mut EF, &mut EF)))| {
            *a_j = tilde_q[3 * j] * tilde_e[3 * j];
            *c_j = tilde_q[3 * j + 1] * tilde_e[3 * j + 1];
            *b_j = tilde_q[3 * j + 2] * tilde_e[3 * j + 2];
        };
        if s < PARALLEL_THRESHOLD {
            a.iter_mut()
                .zip(c_mid.iter_mut().zip(b.iter_mut()))
                .enumerate()
                .for_each(fill);
        } else {
            a.par_iter_mut()
                .zip(c_mid.par_iter_mut().zip(b.par_iter_mut()))
                .enumerate()
                .for_each(fill);
        }
        acc_a[r] = a;
        acc_c[r] = c_mid;
        acc_b[r] = b;

        // MSB-fold Q in place by w_svo[r_f] to drop coord bsvo_{r_F + 1}.
        if r_idx + 1 < l_0 {
            let alpha = group.w_svo[r_f];
            let half = q.len() / 2;
            for i in 0..half {
                let lo = q[i];
                let hi = q[i + half];
                q[i] = lo + alpha * (hi - lo);
            }
            q.truncate(half);
        }
    }
    AccGroup { acc_a, acc_c, acc_b }
}

pub(crate) fn build_accumulators<EF>(groups: &[CompressedGroup<EF>], l_0: usize) -> Vec<AccGroup<EF>>
where
    EF: ExtensionField<PF<EF>>,
{
    groups.par_iter().map(|g| build_accumulators_single(g, l_0)).collect()
}

/// Same as [`round_message`] but takes a precomputed Lagrange tensor. Lets the
/// caller reuse the tensor across rounds via [`lagrange_tensor_extend`].
pub(crate) fn round_message_with_tensor<EF: Field>(r: usize, lagrange: &[EF], accs: &[AccGroup<EF>]) -> (EF, EF, EF) {
    let s = 3_usize.pow(r as u32);
    debug_assert_eq!(lagrange.len(), s);

    let total_work = 3 * s * accs.len();
    let group_reduce = |acc: &AccGroup<EF>| -> (EF, EF, EF) {
        debug_assert_eq!(acc.acc_a[r].len(), s);
        debug_assert_eq!(acc.acc_c[r].len(), s);
        debug_assert_eq!(acc.acc_b[r].len(), s);
        let mut h0 = EF::ZERO;
        let mut h1 = EF::ZERO;
        let mut h2 = EF::ZERO;
        for j in 0..s {
            let l = lagrange[j];
            h0 += l * acc.acc_a[r][j];
            h1 += l * acc.acc_c[r][j];
            h2 += l * acc.acc_b[r][j];
        }
        (h0, h1, h2)
    };
    let add3 = |(a0, a1, a2), (b0, b1, b2)| (a0 + b0, a1 + b1, a2 + b2);
    if total_work < PARALLEL_THRESHOLD {
        accs.iter().map(group_reduce).fold((EF::ZERO, EF::ZERO, EF::ZERO), add3)
    } else {
        accs.par_iter()
            .map(group_reduce)
            .reduce(|| (EF::ZERO, EF::ZERO, EF::ZERO), add3)
    }
}

/// Convert `(h(0), h(1), h(2))` round-polynomial values to `(c_0, c_2)`
/// coefficients of `h(c) = c_0 + c_1 c + c_2 c^2`:
/// `c_0 = h(0)`, `c_2 = (h(2) - 2 h(1) + h(0)) / 2`.
pub(crate) fn values_to_coeffs<EF: Field>(h0: EF, h1: EF, h2: EF) -> (EF, EF) {
    let c0 = h0;
    let c2 = (h2 - h1.double() + h0).halve();
    (c0, c2)
}
