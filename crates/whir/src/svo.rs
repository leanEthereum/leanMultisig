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

// =========================================================================
// Ternary grid primitive (Algorithm 2 "alg:grid" of the tex).
// =========================================================================

/// `{0,1}^l -> {0,1,2}^l` grid expansion of a multilinear function on the
/// boolean hypercube. Input uses big-endian indexing (coord `j` at bit
/// `l-1-j` of the index); output uses `idx = sum_j x_j * 3^j` (coord `x_0`
/// at stride 1, fastest-varying).
///
/// Identity on `{0,1}^l` and extends multilinearly: `f~(..,2,..) =
/// 2*f~(..,1,..) - f~(..,0,..)`. Convenience allocating wrapper used in tests;
/// the hot path calls [`grid_expand_into`] with reusable buffers.
#[cfg(test)]
pub(crate) fn grid_expand<EF: Field>(f: &[EF], l: usize) -> Vec<EF> {
    let out_len = 3_usize.pow(l as u32);
    let mut out = Vec::with_capacity(out_len);
    let mut scratch = Vec::with_capacity(out_len);
    grid_expand_into(f, l, &mut out, &mut scratch);
    out
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
    // Stage buffers ping-pong between `cur` and `nxt`. We pick the pair so
    // that the final write lands in `out`: number of stages is `l`, so the
    // initial `cur` is `scratch` when `l` is odd, `out` when `l` is even —
    // after `l` swaps, `cur` ends up at `out` either way once we adjust.
    // Simpler: always end with a swap that leaves `cur` in `out`. We do this
    // by keeping a single `cur` / `nxt` pair and swapping `out <-> scratch`
    // after the last stage if parity requires it.
    let mut cur: &mut Vec<EF>;
    let mut nxt: &mut Vec<EF>;
    if l.is_multiple_of(2) {
        cur = out;
        nxt = scratch;
    } else {
        cur = scratch;
        nxt = out;
    }
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
        // Parallel only when the stage is big enough — rayon overhead dominates
        // below `PARALLEL_THRESHOLD`.
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
    // cur now holds the final grid; parity was chosen so that cur == out.
    debug_assert_eq!(cur.len(), out_len);
}

// =========================================================================
// Lagrange tensor at nodes {0,1,2} (Algorithm 3 "alg:lagrange").
// =========================================================================

/// Returns `L[i] = prod_{k=0}^{r-1} L_{e_k}(chi_{r-1-k})` on `{0,1,2}^r`,
/// where `i = sum_k e_k * 3^k`. The first `chi` entry ends up at the
/// outermost stride (3^{r-1}); the last at the innermost (3^0).
///
/// Callers invoke this with `chi = (rho_0, rho_1, .., rho_{r-1})` in
/// natural sampling order (under the accumulator's natural feed; see
/// module docstring). The hot path in `open.rs` calls
/// [`lagrange_tensor_extend`] incrementally instead.
#[cfg(test)]
pub(crate) fn lagrange_tensor<EF: Field>(chi: &[EF]) -> Vec<EF> {
    let mut out = vec![EF::ONE];
    for &c in chi {
        lagrange_tensor_extend(&mut out, c);
    }
    out
}

/// Extend a `3^r`-size Lagrange tensor to `3^{r+1}` by tensoring with the
/// `(L_0, L_1, L_2)` triple at `c`. Mirrors [`lagrange_tensor`] one step at a
/// time, lets the round loop amortize allocations.
pub(crate) fn lagrange_tensor_extend<EF: Field>(out: &mut Vec<EF>, c: EF) {
    // L_0(c) = (c-1)(c-2)/2, L_1(c) = c(2-c), L_2(c) = c(c-1)/2.
    let inv_two = EF::TWO.inverse();
    let two = EF::TWO;
    let c_m1 = c - EF::ONE;
    let c_m2 = c - two;
    let l0 = c_m1 * c_m2 * inv_two;
    let l1 = c * (two - c);
    let l2 = c * c_m1 * inv_two;
    let mut new = Vec::with_capacity(out.len() * 3);
    for &v in out.iter() {
        new.push(v * l0);
        new.push(v * l1);
        new.push(v * l2);
    }
    *out = new;
}

// =========================================================================
// eq-claim compression (Algorithm 1 "alg:compress_sparse" + merge).
// =========================================================================

/// For one eq-claim group: `K` selectors sharing an inner point `p ∈ Fq^{m}`
/// with `m = l - s`. Builds the merged compressed polynomial
///
///   p_bar[bsvo] = sum_j alpha_j * sum_{b' in {0,1}^{l - l_0 - s}}
///                 eq(b', p_split) * f(sel_j, b', bsvo)
///
/// where `p_split = p[0..m - l_0]` and `p_svo = p[m - l_0..m]`. Returns
/// `CompressedGroup { w_svo: p_svo.to_vec(), p_bar }`.
/// One `CompressedGroup` per eq-claim **group** when `s <= l - l_0` (the
/// non-spill regime). Merges all `K` selectors in the group via the shared
/// `E_split` table (Algorithm 2 "alg:merge").
///
/// For the complementary `s > l - l_0` regime (selector spills into `wsvo`),
/// use [`compress_eq_spill_claim`] — one group per claim, since claims with
/// different spilled bits have different `wsvo` and cannot be merged.
#[allow(clippy::too_many_arguments)]
pub(crate) fn compress_eq_claim<EF>(
    f_base: Option<&[PF<EF>]>,
    f_ext: Option<&[EF]>,
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

    // Shared eq-table over the split-side extension coords.
    // length 2^{m_split}
    let e_split: Vec<EF> = if m_split == 0 { vec![EF::ONE] } else { eval_eq(p_split) };
    let e_len = e_split.len();
    let svo_len = 1usize << l_0;
    let mut p_bar = vec![EF::ZERO; svo_len];

    // For each claim, walk β_split (outer) and bsvo (inner) so f reads stride
    // 1 (sequential) rather than 2^{l_0}. Per-tile we hold an `svo_len` partial
    // sum; tiles reduce with pointwise addition.
    // Parallelism granularity: total inner work per claim is
    // `e_len * svo_len = 2^{l-s}` field products. Fall back to serial when
    // below `PARALLEL_THRESHOLD`.
    let total_inner = e_len * svo_len;
    for (&sel_j, &alpha_j) in sel_bits.iter().zip(alpha_powers.iter()) {
        let sel_offset = sel_j << (l - s);
        let svo_contrib: Vec<EF> = if total_inner < PARALLEL_THRESHOLD {
            let mut acc = vec![EF::ZERO; svo_len];
            for b in 0..e_len {
                let e = e_split[b];
                let base = sel_offset + (b << l_0);
                if let Some(fb) = f_base {
                    let row = &fb[base..base + svo_len];
                    for bsvo in 0..svo_len {
                        acc[bsvo] += e * row[bsvo];
                    }
                } else if let Some(fe) = f_ext {
                    let row = &fe[base..base + svo_len];
                    for bsvo in 0..svo_len {
                        acc[bsvo] += e * row[bsvo];
                    }
                }
            }
            acc
        } else {
            (0..e_len)
                .into_par_iter()
                .fold(
                    || vec![EF::ZERO; svo_len],
                    |mut acc, b| {
                        let e = e_split[b];
                        let base = sel_offset + (b << l_0);
                        if let Some(fb) = f_base {
                            let row = &fb[base..base + svo_len];
                            for bsvo in 0..svo_len {
                                acc[bsvo] += e * row[bsvo];
                            }
                        } else if let Some(fe) = f_ext {
                            let row = &fe[base..base + svo_len];
                            for bsvo in 0..svo_len {
                                acc[bsvo] += e * row[bsvo];
                            }
                        }
                        acc
                    },
                )
                .reduce(
                    || vec![EF::ZERO; svo_len],
                    |mut a, b| {
                        for (x, y) in a.iter_mut().zip(b.iter()) {
                            *x += *y;
                        }
                        a
                    },
                )
        };
        for (p, s) in p_bar.iter_mut().zip(svo_contrib.iter()) {
            *p += alpha_j * *s;
        }
    }

    CompressedGroup {
        w_svo: p_svo.to_vec(),
        p_bar,
    }
}

/// Spill-regime eq-claim: `s > l - l_0`. Selector's top `l - l_0` bits pin
/// the entire split block (boolean-indicator `eq`); the bottom `s - (l - l_0)`
/// bits spill into `wsvo` as boolean EF coordinates. `inner_point` (length
/// `m = l - s < l_0`) fills `wsvo`'s remaining trailing coords.
///
/// Emits **one CompressedGroup per claim** (claims with different spilled
/// bits have different `wsvo` and cannot share a `p_bar`).
#[allow(clippy::too_many_arguments)]
pub(crate) fn compress_eq_spill_claim<EF>(
    f_base: Option<&[PF<EF>]>,
    f_ext: Option<&[EF]>,
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
    assert!(s > l - l_0, "compress_eq_spill_claim requires s > l - l_0");
    let m = l - s;
    assert_eq!(inner_point.len(), m);
    let s_split_bool = l - l_0;
    let s_svo_bool = s - s_split_bool;
    debug_assert_eq!(s_svo_bool + m, l_0);

    let svo_len = 1usize << l_0;
    let mut out: Vec<CompressedGroup<EF>> = Vec::with_capacity(sel_bits.len());
    for (&sel_j, &alpha_j) in sel_bits.iter().zip(alpha_powers.iter()) {
        // Decompose selector into (top = sel_split_bool part, bottom = sel_svo_bool part).
        let sel_top = sel_j >> s_svo_bool;
        let sel_bot = sel_j & ((1usize << s_svo_bool) - 1);

        // w_svo layout: [spilled bool bits (s_svo_bool) | inner_point (m)], total l_0. Under our
        // big-endian `wsvo` convention, the first coord (bsvo_1, MSB of bsvo index) is the
        // highest-significance spilled bit; the m trailing coords are inner_point in order.
        let mut w_svo: Vec<EF> = Vec::with_capacity(l_0);
        for k in 0..s_svo_bool {
            let bit = ((sel_bot >> (s_svo_bool - 1 - k)) & 1) as u32;
            w_svo.push(if bit == 1 { EF::ONE } else { EF::ZERO });
        }
        w_svo.extend_from_slice(inner_point);
        debug_assert_eq!(w_svo.len(), l_0);

        // p_bar[bsvo] = alpha_j * f[sel_top * 2^{l_0} + bsvo]. Simple slice read scaled by alpha.
        let sel_offset = sel_top << l_0;
        let mut p_bar: Vec<EF> = Vec::with_capacity(svo_len);
        for bsvo in 0..svo_len {
            let idx = sel_offset + bsvo;
            let v: EF = if let Some(fb) = f_base {
                EF::from(fb[idx])
            } else if let Some(fe) = f_ext {
                fe[idx]
            } else {
                unreachable!()
            };
            p_bar.push(alpha_j * v);
        }
        out.push(CompressedGroup { w_svo, p_bar });
    }
    out
}

// =========================================================================
// nxt-claim bucketed compression (Algorithm 4 "alg:next_bucketed").
// =========================================================================

/// For one nxt-claim group: `K` selectors sharing inner point `p ∈ Fq^m`.
/// Emits `K * 0 + (l_0 + 2)` sub-groups — one shared Σ_split, `l_0` bucket-B
/// sub-groups sharing `P_eq`, one bucket-C slice — with the per-claim α-weighted
/// sums over the group's selectors merged inside.
///
/// Returns exactly `l_0 + 2` `CompressedGroup`s.
#[allow(clippy::too_many_arguments)]
pub(crate) fn compress_next_claim_bucketed<EF>(
    f_base: Option<&[PF<EF>]>,
    f_ext: Option<&[EF]>,
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
    //   bar_T_split[β] = sum_{J in [0, m_split)} c[J] * T_J^split(β).
    //   E_split[β] = eq(β, p[0..m_split]).
    //   c_omega = prod_{j=0..m-1} p[j].
    //   c[J] = (prod_{j>J, j<m} p[j]) * (1 - p[J]).
    let bar_t_split = build_bar_t_split(inner_point, m_split, m);
    let e_split: Vec<EF> = if m_split == 0 {
        vec![EF::ONE]
    } else {
        eval_eq(&inner_point[..m_split])
    };
    debug_assert_eq!(bar_t_split.len(), split_len);
    debug_assert_eq!(e_split.len(), split_len);

    let c_omega: EF = inner_point.iter().copied().product::<EF>();

    // Bucket-B per-pivot scalars c[J] for J in [m_split, m).
    let c_pivot: Vec<EF> = (m_split..m)
        .map(|j| {
            let tail: EF = inner_point[j + 1..].iter().copied().product();
            (EF::ONE - inner_point[j]) * tail
        })
        .collect();

    // Accumulators (α-weighted over K claims at the bsvo level).
    let mut sigma_split = vec![EF::ZERO; svo_len];
    let mut p_eq = vec![EF::ZERO; svo_len];
    let mut s_omega = vec![EF::ZERO; svo_len];

    let total_inner = split_len * svo_len;
    for (&sel_j, &alpha_j) in sel_bits.iter().zip(alpha_powers.iter()) {
        let sel_offset = sel_j << (l - s);

        // Fused pass: outer b_split, inner bsvo — sequential reads of f in the
        // inner loop. Per tile we carry two size-`svo_len` partial sums.
        let (sig_contrib, eq_contrib): (Vec<EF>, Vec<EF>) = if total_inner < PARALLEL_THRESHOLD {
            let mut sig = vec![EF::ZERO; svo_len];
            let mut eq_acc = vec![EF::ZERO; svo_len];
            for b in 0..split_len {
                let bt = bar_t_split[b];
                let et = e_split[b];
                let base = sel_offset + (b << l_0);
                if let Some(fb) = f_base {
                    let row = &fb[base..base + svo_len];
                    for bsvo in 0..svo_len {
                        let v = row[bsvo];
                        sig[bsvo] += bt * v;
                        eq_acc[bsvo] += et * v;
                    }
                } else if let Some(fe) = f_ext {
                    let row = &fe[base..base + svo_len];
                    for bsvo in 0..svo_len {
                        let v = row[bsvo];
                        sig[bsvo] += bt * v;
                        eq_acc[bsvo] += et * v;
                    }
                }
            }
            (sig, eq_acc)
        } else {
            (0..split_len)
                .into_par_iter()
                .fold(
                    || (vec![EF::ZERO; svo_len], vec![EF::ZERO; svo_len]),
                    |(mut sig, mut eq_acc), b| {
                        let bt = bar_t_split[b];
                        let et = e_split[b];
                        let base = sel_offset + (b << l_0);
                        if let Some(fb) = f_base {
                            let row = &fb[base..base + svo_len];
                            for bsvo in 0..svo_len {
                                let v = row[bsvo];
                                sig[bsvo] += bt * v;
                                eq_acc[bsvo] += et * v;
                            }
                        } else if let Some(fe) = f_ext {
                            let row = &fe[base..base + svo_len];
                            for bsvo in 0..svo_len {
                                let v = row[bsvo];
                                sig[bsvo] += bt * v;
                                eq_acc[bsvo] += et * v;
                            }
                        }
                        (sig, eq_acc)
                    },
                )
                .reduce(
                    || (vec![EF::ZERO; svo_len], vec![EF::ZERO; svo_len]),
                    |(mut a_s, mut a_e), (b_s, b_e)| {
                        for (x, y) in a_s.iter_mut().zip(b_s.iter()) {
                            *x += *y;
                        }
                        for (x, y) in a_e.iter_mut().zip(b_e.iter()) {
                            *x += *y;
                        }
                        (a_s, a_e)
                    },
                )
        };

        // Bucket-C: slice read at β_split = 1^{m_split} (all split-bits set).
        let b_all_ones = split_len - 1;
        let c_base = sel_offset + (b_all_ones << l_0);
        for bsvo in 0..svo_len {
            let v = if let Some(fb) = f_base {
                EF::from(fb[c_base + bsvo])
            } else if let Some(fe) = f_ext {
                fe[c_base + bsvo]
            } else {
                unreachable!()
            };
            s_omega[bsvo] += alpha_j * v;
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
    // Bucket B: one sub-group per j* in {m_split+1, .., m} (1-indexed), i.e.
    //   pivot_0idx J in [m_split, m); pivot_pos = J - m_split in [0, l_0).
    for (k, &cp) in c_pivot.iter().enumerate() {
        let pivot_pos = k; // = J - m_split
        let mut w = vec![EF::ZERO; l_0];
        for coord in 0..l_0 {
            if coord < pivot_pos {
                // w^(j*)_{coord+1} = p_{m_split + coord + 1}  (1-indexed)
                // = inner_point[m_split + coord] (0-indexed).
                w[coord] = inner_point[m_split + coord];
            } else if coord == pivot_pos {
                w[coord] = EF::ONE;
            } else {
                w[coord] = EF::ZERO;
            }
        }
        let mut pb = p_eq.clone();
        for v in pb.iter_mut() {
            *v *= cp;
        }
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

/// Build `bar_T_split[β] = sum_{J < m_split} c[J] * T_J^split(β)` where
///   c[J] = (prod_{j>J, j<m} p[j]) * (1 - p[J])
///   T_J^split(β) = prod_{j<J} eq(p[j], β[j]) * β[J] * prod_{j>J, j<m_split} (1-β[j]).
///
/// For every β, exactly one pivot J contributes (the position of the last
/// `1` in β among coords `[0, m_split)`): all coords after J must be 0 to
/// avoid the `(1-β)` factor, and β[J] must be 1. So the table is
///
///   bar_T[β] = c[J_last_1(β)] * prod_{j<J_last_1(β)} eq(p[j], β[j])    if β ≠ 0
///            = 0                                                         else.
///
/// Filled with an incremental sweep over J in `[0, m_split)`, using
/// eq_prefix_J = eval_eq(p[0..J]) (size 2^J). Total work: `O(2^{m_split})` ee.
fn build_bar_t_split<EF: Field>(p: &[EF], m_split: usize, m: usize) -> Vec<EF> {
    let out_len = 1usize << m_split;
    let mut bar_t = vec![EF::ZERO; out_len];

    // Suffix products: suf[j] = prod_{j'=j..m} p[j'], with suf[m] = 1.
    let mut suf = vec![EF::ONE; m + 1];
    for j in (0..m).rev() {
        suf[j] = suf[j + 1] * p[j];
    }
    // c[J] for J in [0, m_split)
    // Note: "c[J]" here encodes the pivot on the split side.
    // c[J] = (prod_{j' > J, j' < m} p[j']) * (1 - p[J]) = suf[J+1] * (1 - p[J]).
    // Also compute the prefix eq-table incrementally, size 2^J.
    let mut prefix = vec![EF::ONE]; // eval_eq on 0 coords.
    for j in 0..m_split {
        let c_j = suf[j + 1] * (EF::ONE - p[j]);
        let stride = 1usize << (m_split - j);
        let offset = 1usize << (m_split - 1 - j);
        // Fill bar_t[k * stride + offset] = c_j * prefix[k] for k in [0, 2^j).
        let prefix_len = prefix.len();
        debug_assert_eq!(prefix_len, 1 << j);
        for k in 0..prefix_len {
            bar_t[k * stride + offset] = c_j * prefix[k];
        }
        // Extend prefix to eval_eq(p[0..j+1]) if we'll use it next iteration.
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
    bar_t
}

// =========================================================================
// Per-round accumulators (Algorithm 5 "alg:accs").
// =========================================================================

/// For a single group, build `{acc_a[r], acc_b[r]}` for `r = 0..l_0`, each
/// of length `3^r`. Pattern per round (using the NATURAL feed layout — see
/// module docstring):
///   Q_r = P_bar partially-evaluated on the first `r_F = l_0 - r - 1` coords
///         (in Q's natural big-endian: the LEADING coords of the bsvo array).
///         Size 2^{r+1}.
///   E_r = eval_eq(w_svo[r_F..l_0])       size 2^{r+1}.
///   tilde_Q, tilde_E = grid_expand(..)   size 3^{r+1}.
///   acc_a[r][j] = tilde_Q[3j] * tilde_E[3j]
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

    // Q starts as P_bar (size 2^{l_0}, r = l_0 - 1, r_F = 0). Each iteration
    // emits the current Q as Q_r then MSB-folds by w_svo[r_F] to advance to
    // r-1 (r_F += 1).
    //
    // Persistent buffers reused across rounds: `q` shrinks in place (MSB-fold
    // via `truncate`); `tilde_q` / `tilde_e` and their scratch are kept at
    // `3^{l_0}` capacity to avoid per-round allocs inside `grid_expand`.
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

        // E at round r: eq-table over w_svo[r_f..l_0], big-endian.
        // Reuse `e_buf` instead of allocating a fresh Vec via `eval_eq`.
        e_buf.clear();
        e_buf.resize(1 << big_l, EF::ZERO);
        compute_eval_eq::<PF<EF>, EF, false>(&group.w_svo[r_f..], &mut e_buf, EF::ONE);

        grid_expand_into(&q, big_l, &mut tilde_q, &mut scratch_q);
        grid_expand_into(&e_buf, big_l, &mut tilde_e, &mut scratch_e);
        let s = 3_usize.pow(r as u32);
        let mut a = Vec::with_capacity(s);
        let mut c_mid = Vec::with_capacity(s);
        let mut b = Vec::with_capacity(s);
        for j in 0..s {
            a.push(tilde_q[3 * j] * tilde_e[3 * j]);
            c_mid.push(tilde_q[3 * j + 1] * tilde_e[3 * j + 1]);
            b.push(tilde_q[3 * j + 2] * tilde_e[3 * j + 2]);
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

// =========================================================================
// Round message (Algorithm 6 "alg:round").
// =========================================================================

/// `rhos.len() == r`. Returns `(h(0), h(1), h(2))` — the round polynomial
/// evaluated at the interpolation nodes `{0, 1, 2}`. Independent of any
/// running-sum invariant, so this is self-consistent for tests even when
/// the statements' values are not polynomial-consistent.
#[cfg(test)]
pub(crate) fn round_message<EF: Field>(r: usize, rhos: &[EF], accs: &[AccGroup<EF>]) -> (EF, EF, EF) {
    assert_eq!(rhos.len(), r);
    // Under natural feed layout, pass rhos in sampling order.
    let lagrange = lagrange_tensor(rhos);
    round_message_with_tensor(r, &lagrange, accs)
}

/// Same as [`round_message`] but takes a precomputed Lagrange tensor. Lets the
/// caller reuse the tensor across rounds via [`lagrange_tensor_extend`].
pub(crate) fn round_message_with_tensor<EF: Field>(r: usize, lagrange: &[EF], accs: &[AccGroup<EF>]) -> (EF, EF, EF) {
    let s = 3_usize.pow(r as u32);
    debug_assert_eq!(lagrange.len(), s);

    // Per-group work is `3s` ee-products; total = `3 * s * accs.len()`. Go
    // parallel across groups when this exceeds `PARALLEL_THRESHOLD`; otherwise
    // stay serial to avoid rayon overhead on tiny rounds.
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
    if total_work < PARALLEL_THRESHOLD {
        accs.iter()
            .map(group_reduce)
            .fold((EF::ZERO, EF::ZERO, EF::ZERO), |(a0, a1, a2), (b0, b1, b2)| {
                (a0 + b0, a1 + b1, a2 + b2)
            })
    } else {
        accs.par_iter().map(group_reduce).reduce(
            || (EF::ZERO, EF::ZERO, EF::ZERO),
            |(a0, a1, a2), (b0, b1, b2)| (a0 + b0, a1 + b1, a2 + b2),
        )
    }
}

/// Convert `(h(0), h(1), h(2))` round-polynomial values to `(c_0, c_2)`
/// coefficients of `h(c) = c_0 + c_1 c + c_2 c^2`.
/// `c_0 = h(0)`, `c_2 = (h(2) - 2 h(1) + h(0)) / 2`.
pub(crate) fn values_to_coeffs<EF: Field>(h0: EF, h1: EF, h2: EF) -> (EF, EF) {
    let c0 = h0;
    let c2 = (h2 - h1.double() + h0).halve();
    (c0, c2)
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use field::PrimeCharacteristicRing;
    use koala_bear::QuinticExtensionFieldKB;
    use poly::matrix_next_mle_folded;
    use rand::{RngExt, SeedableRng, rngs::StdRng};

    type F = koala_bear::KoalaBear;
    type EF = QuinticExtensionFieldKB;

    // Brute-force ternary-grid expansion: f~(x) = sum over 2^l corners of
    // f(corner) * prod_k basis_{x_k}(corner_k), where basis is the Lagrange
    // basis at {0,1} interpolated to {0,1,2} multilinearly.
    fn brute_grid<EF: Field>(f: &[EF], l: usize) -> Vec<EF> {
        let out_len = 3_usize.pow(l as u32);
        let mut out = vec![EF::ZERO; out_len];
        // Multilinear extension at x ∈ {0,1,2}^l: MLE at x = sum_{b∈{0,1}^l} f(b) * prod_k basis(b_k, x_k)
        // with basis(0, 0)=1, basis(0, 1)=0, basis(0, 2)=-1, basis(1, 0)=0, basis(1, 1)=1, basis(1, 2)=2.
        // I.e. basis(b, x) = (1 - x) if b=0, x if b=1, when x ∈ {0,1,2} and the MLE is degree 1 in x.
        for i in 0..out_len {
            // decode x_j: stride 3^j -> x_j in {0,1,2}
            let mut xs = vec![0u8; l];
            let mut ii = i;
            for j in 0..l {
                xs[j] = (ii % 3) as u8;
                ii /= 3;
            }
            let mut acc = EF::ZERO;
            for bi in 0..(1 << l) {
                // input big-endian: b_j = (bi >> (l-1-j)) & 1
                let mut weight = EF::ONE;
                for j in 0..l {
                    let bj = ((bi >> (l - 1 - j)) & 1) as u8;
                    let xj = xs[j];
                    // basis: b=0 -> (1 - xj), b=1 -> xj, evaluated at xj ∈ {0,1,2}
                    let w = match (bj, xj) {
                        (0, 0) => EF::ONE,
                        (0, 1) => EF::ZERO,
                        (0, 2) => EF::ZERO - EF::ONE,
                        (1, 0) => EF::ZERO,
                        (1, 1) => EF::ONE,
                        (1, 2) => EF::TWO,
                        _ => unreachable!(),
                    };
                    weight *= w;
                }
                acc += weight * f[bi];
            }
            out[i] = acc;
        }
        out
    }

    #[test]
    fn grid_expand_matches_brute_force() {
        let mut rng = StdRng::seed_from_u64(7);
        for l in 0..5 {
            let f: Vec<EF> = (0..(1u64 << l)).map(|_| rng.random::<EF>()).collect();
            let fast = grid_expand(&f, l);
            let slow = brute_grid(&f, l);
            assert_eq!(fast, slow, "grid_expand mismatch at l={l}");
        }
    }

    #[test]
    fn grid_expand_preserves_boolean_values() {
        // For i in {0,1}^l (represented in base 3 with digits in {0,1}), f~[i]
        // should equal f[bi_bigend(digits)].
        let mut rng = StdRng::seed_from_u64(8);
        for l in 0..5 {
            let f: Vec<EF> = (0..(1u64 << l)).map(|_| rng.random::<EF>()).collect();
            let out = grid_expand(&f, l);
            for bi in 0..(1usize << l) {
                // Input index in big-endian: b_j = (bi >> (l-1-j)) & 1.
                // Output index: i = sum_j b_j * 3^j.
                let mut oi = 0usize;
                let mut pow3 = 1usize;
                for j in 0..l {
                    let bj = (bi >> (l - 1 - j)) & 1;
                    oi += bj * pow3;
                    pow3 *= 3;
                }
                assert_eq!(out[oi], f[bi], "bool-corner mismatch at l={l} bi={bi}");
            }
        }
    }

    fn lagrange_brute<EF: Field>(chi: &[EF]) -> Vec<EF> {
        // L[i] = prod_{k=0}^{r-1} L_{e_k}(chi_{r-1-k}) where i = sum e_k * 3^k.
        let r = chi.len();
        let size = 3_usize.pow(r as u32);
        let inv_two = EF::TWO.inverse();
        let mut out = vec![EF::ZERO; size];
        for i in 0..size {
            let mut ii = i;
            let mut weight = EF::ONE;
            for k in 0..r {
                let e_k = ii % 3;
                ii /= 3;
                let c = chi[r - 1 - k];
                let l_val = match e_k {
                    0 => (c - EF::ONE) * (c - EF::TWO) * inv_two,
                    1 => c * (EF::TWO - c),
                    2 => c * (c - EF::ONE) * inv_two,
                    _ => unreachable!(),
                };
                weight *= l_val;
            }
            out[i] = weight;
        }
        out
    }

    #[test]
    fn lagrange_tensor_matches_brute() {
        let mut rng = StdRng::seed_from_u64(9);
        for r in 0..5 {
            let chi: Vec<EF> = (0..r).map(|_| rng.random::<EF>()).collect();
            let fast = lagrange_tensor(&chi);
            let slow = lagrange_brute(&chi);
            assert_eq!(fast, slow, "lagrange mismatch at r={r}");
        }
    }

    // NOTE: there is no `lagrange_at_boolean_equals_multilinear_eq` test —
    // L_0(c) is the degree-2 Lagrange basis at node 0 over {0,1,2}, so
    // L_0(chi) = (chi-1)(chi-2)/2 for chi in Fq, NOT 1 - chi. The eq-like
    // relation only holds at chi ∈ {0,1,2}, not for general extension chi.

    /// Brute: compute the round-`r` polynomial `h_r(c)` at `c ∈ {0, 2}`
    /// directly from the polynomial definition of
    /// `Phi(bsvo) = sum_g eq(bsvo, w_svo_g) * p_bar_g(bsvo)` (with both
    /// factors multilinear in bsvo, so Phi is degree 2 per coord).
    ///
    /// At round `r` under LSB-fold convention the active coord is
    /// `bsvo_{l_0 - r}`; already-sampled `rho_0, .., rho_{r-1}` are pinned
    /// at coords `bsvo_{l_0}, bsvo_{l_0 - 1}, ..., bsvo_{l_0 - r + 1}`.
    ///
    /// h_r(c) = sum_{b_F ∈ {0,1}^{l_0-r-1}}
    ///           sum_g eq_of_bsvo_poly * p_bar_of_bsvo_poly
    /// where bsvo = (b_F_0, .., b_F_{r_F-1}, c, rho_{r-1}, .., rho_0)
    /// under natural big-endian ordering (b_F at the leading coords, rho_0 at the last).
    fn brute_round_c0_c2<EF>(groups: &[CompressedGroup<EF>], l_0: usize, r: usize, rhos: &[EF]) -> (EF, EF)
    where
        EF: ExtensionField<PF<EF>>,
    {
        assert_eq!(rhos.len(), r);
        let r_f = l_0 - r - 1;
        // For each c ∈ {0, 2} and each free-coord assignment b_F, evaluate Phi at
        // bsvo = (b_F_0, .., b_F_{r_F-1}, c, rho_{r-1}, .., rho_0).
        let mut h_at = [EF::ZERO, EF::ZERO]; // h(0), h(2)

        for (idx, &c_val) in [EF::ZERO, EF::TWO].iter().enumerate() {
            let mut h = EF::ZERO;
            for b_f_mask in 0..(1usize << r_f) {
                // Build bsvo point (length l_0), natural big-endian: bsvo_1 at position 0.
                let mut bsvo_point: Vec<EF> = Vec::with_capacity(l_0);
                for k in 0..r_f {
                    // b_F_k at natural-big-endian position k.
                    let bit = ((b_f_mask >> (r_f - 1 - k)) & 1) as u32;
                    bsvo_point.push(if bit == 1 { EF::ONE } else { EF::ZERO });
                }
                // active at position r_f
                bsvo_point.push(c_val);
                // rho slots: bsvo_{l_0 - r + 1} .. bsvo_{l_0} hold rho_{r-1} .. rho_0.
                // At natural positions (r_f + 1) .. (l_0 - 1), values rho_{r-1} .. rho_0.
                for k in 0..r {
                    bsvo_point.push(rhos[r - 1 - k]);
                }
                assert_eq!(bsvo_point.len(), l_0);

                for g in groups {
                    // eq_poly(bsvo_point, w_svo_g)
                    let mut eq_val = EF::ONE;
                    for k in 0..l_0 {
                        let x = bsvo_point[k];
                        let w = g.w_svo[k];
                        eq_val *= x * w + (EF::ONE - x) * (EF::ONE - w);
                    }
                    // p_bar_g evaluated at bsvo_point (MLE of the size-2^{l_0} table).
                    let p_val = mle_eval(&g.p_bar, &bsvo_point);
                    h += eq_val * p_val;
                }
            }
            h_at[idx] = h;
        }
        (h_at[0], h_at[1])
    }

    /// Evaluate the multilinear extension of a size-2^n boolean-corner table
    /// `f` at a point `x ∈ F^n` (big-endian: x_0 is the MSB of the index).
    fn mle_eval<EF>(f: &[EF], x: &[EF]) -> EF
    where
        EF: ExtensionField<PF<EF>>,
    {
        let n = x.len();
        assert_eq!(f.len(), 1 << n);
        // Sum over boolean corners b: f[b] * prod_k (x_k if b_k=1 else 1 - x_k).
        let mut acc = EF::ZERO;
        for b in 0..(1usize << n) {
            let mut w = EF::ONE;
            for k in 0..n {
                let bit = ((b >> (n - 1 - k)) & 1) as u32;
                w *= if bit == 1 { x[k] } else { EF::ONE - x[k] };
            }
            acc += w * f[b];
        }
        acc
    }

    #[test]
    fn round0_matches_brute() {
        let mut rng = StdRng::seed_from_u64(11);
        for l_0 in 1..=5 {
            let g_count = 3;
            let groups: Vec<CompressedGroup<EF>> = (0..g_count)
                .map(|_| CompressedGroup {
                    w_svo: (0..l_0).map(|_| rng.random::<EF>()).collect(),
                    p_bar: (0..(1 << l_0)).map(|_| rng.random::<EF>()).collect(),
                })
                .collect();
            let accs = build_accumulators(&groups, l_0);
            let (h0, _h1, h2) = round_message(0, &[], &accs);
            let (h0_brute, h2_brute) = brute_round_c0_c2(&groups, l_0, 0, &[]);
            assert_eq!(h0, h0_brute, "round 0 h(0) mismatch at l_0={l_0}");
            assert_eq!(h2, h2_brute, "round 0 h(2) mismatch at l_0={l_0}");
        }
    }

    /// Round-by-round: after sampling `rho_r`, the "running" polynomial is
    /// Phi partially evaluated at rho_r on the active coord. This check compares
    /// SVO's `round_message` output against a direct polynomial evaluation at
    /// the (b_F, c, rho_{r-1}..rho_0) point over Phi = sum_g eq * p_bar.
    #[test]
    fn svo_rounds_match_polynomial() {
        let mut rng = StdRng::seed_from_u64(12);
        for l_0 in 1..=4 {
            for _trial in 0..3 {
                let g_count = 1 + rng.random_range(0usize..3);
                let groups: Vec<CompressedGroup<EF>> = (0..g_count)
                    .map(|_| CompressedGroup {
                        w_svo: (0..l_0).map(|_| rng.random::<EF>()).collect(),
                        p_bar: (0..(1 << l_0)).map(|_| rng.random::<EF>()).collect(),
                    })
                    .collect();
                let accs = build_accumulators(&groups, l_0);
                let mut rhos: Vec<EF> = Vec::new();
                for r in 0..l_0 {
                    let (h0_svo, _h1_svo, h2_svo) = round_message(r, &rhos, &accs);
                    let (h0_brute, h2_brute) = brute_round_c0_c2(&groups, l_0, r, &rhos);
                    assert_eq!(h0_svo, h0_brute, "h(0) mismatch at l_0={l_0}, r={r}");
                    assert_eq!(h2_svo, h2_brute, "h(2) mismatch at l_0={l_0}, r={r}");
                    let rho: EF = rng.random();
                    rhos.push(rho);
                }
            }
        }
    }

    // Check `compress_eq_claim` against a direct brute-force build of p_bar.
    #[test]
    fn compress_eq_claim_matches_brute() {
        let mut rng = StdRng::seed_from_u64(13);
        for l in 4..=8 {
            for l_0 in 1..=(l / 2).min(4) {
                for s in 0..=(l - l_0) {
                    for _trial in 0..2 {
                        let m = l - s;
                        let inner_point: Vec<EF> = (0..m).map(|_| rng.random::<EF>()).collect();
                        let k = 2.min(1 << s);
                        let mut used = Vec::new();
                        while used.len() < k {
                            let sel = if s == 0 { 0 } else { rng.random_range(0..(1usize << s)) };
                            if !used.contains(&sel) {
                                used.push(sel);
                            }
                        }
                        let alphas: Vec<EF> = (0..k).map(|_| rng.random::<EF>()).collect();
                        let f: Vec<F> = (0..(1 << l)).map(|_| rng.random::<F>()).collect();

                        let got = compress_eq_claim::<EF>(Some(&f), None, &used, &inner_point, &alphas, l, l_0, s);

                        // Brute: p_bar[bsvo] = sum_j alpha_j * sum_{b ∈ {0,1}^m} eq(b, inner_point) *
                        //                                       f[(sel_j << m) + (b << l_0 -> nope wait)]
                        // Actually per tex: p_bar[bsvo] = sum_j alpha_j * sum_{b' ∈ {0,1}^{m_split}}
                        //                                       eq(b', p_split) * f[sel_j, b', bsvo].
                        // Cross-check with a fully brute form: p_bar[bsvo] = sum_j alpha_j *
                        //   eq_over_inner(partial-eval)... equivalently the naive sum over b ∈ {0,1}^m
                        //   of eq((sel_j || b), (sel_j || inner_point)) * f(sel_j || b || bsvo) with
                        //   the (sel_j || ·) in b pinned to sel_j. Under the tex's claim this reduces
                        //   to the m_split-sum.
                        let m_split = l - l_0 - s;
                        let e_split_slow: Vec<EF> = if m_split == 0 {
                            vec![EF::ONE]
                        } else {
                            eval_eq(&inner_point[..m_split])
                        };
                        let p_svo = &inner_point[m_split..m];
                        let mut expected = vec![EF::ZERO; 1 << l_0];
                        for (&sel_j, &alpha_j) in used.iter().zip(alphas.iter()) {
                            for bsvo in 0..(1usize << l_0) {
                                let mut s_j = EF::ZERO;
                                for b in 0..(1usize << m_split) {
                                    let idx = (sel_j << (l - s)) + (b << l_0) + bsvo;
                                    s_j += e_split_slow[b] * f[idx];
                                }
                                expected[bsvo] += alpha_j * s_j;
                            }
                        }
                        assert_eq!(got.p_bar, expected, "p_bar mismatch at l={l} l_0={l_0} s={s}");
                        assert_eq!(got.w_svo, p_svo.to_vec());
                    }
                }
            }
        }
    }

    #[test]
    fn compress_eq_spill_matches_brute() {
        // Selector spills into wsvo: s > l - l_0. Verify that the emitted
        // CompressedGroups sum to the same Phi(bsvo) as the direct formula.
        let mut rng = StdRng::seed_from_u64(15);
        for l in 4..=8 {
            for l_0 in 1..=(l - 1).min(4) {
                for s in (l - l_0 + 1)..=l {
                    let m = l - s;
                    let inner_point: Vec<EF> = (0..m).map(|_| rng.random::<EF>()).collect();
                    let k = 2.min(1 << s);
                    let mut used = Vec::new();
                    while used.len() < k {
                        let sel = rng.random_range(0..(1usize << s));
                        if !used.contains(&sel) {
                            used.push(sel);
                        }
                    }
                    let alphas: Vec<EF> = (0..k).map(|_| rng.random::<EF>()).collect();
                    let f: Vec<F> = (0..(1 << l)).map(|_| rng.random::<F>()).collect();

                    let groups = compress_eq_spill_claim::<EF>(Some(&f), None, &used, &inner_point, &alphas, l, l_0, s);
                    assert_eq!(groups.len(), k);

                    // Sum emitted sub-groups as Phi(bsvo).
                    let mut phi = vec![EF::ZERO; 1 << l_0];
                    for g in &groups {
                        let e = eval_eq(&g.w_svo);
                        for i in 0..(1 << l_0) {
                            phi[i] += e[i] * g.p_bar[i];
                        }
                    }

                    // Brute: Phi(bsvo) = sum_j alpha_j * sum_{b in {0,1}^{l-l_0}}
                    //   eq((b, bsvo), (sel_top_bool, sel_bot_bool, inner_point)) * f[(sel_j << (l-s)) + inner_shift_to_get_idx].
                    // Simpler: each claim asserts f[(sel_j << (l-s)) + inner_as_bits] = scalar,
                    // but when inner_point is extension, the "scalar" depends on inner MLE evaluation.
                    // Let's just compute directly: Phi_direct(bsvo) = sum_j alpha_j * eq(bsvo, wsvo_j) * f_slice_j[bsvo].
                    let s_svo_bool = s - (l - l_0);
                    let mut expected = vec![EF::ZERO; 1 << l_0];
                    for (&sel_j, &alpha_j) in used.iter().zip(alphas.iter()) {
                        let sel_top = sel_j >> s_svo_bool;
                        let sel_bot = sel_j & ((1usize << s_svo_bool) - 1);
                        // wsvo = (sel_bot_as_bool_bits, inner_point)
                        let mut w_svo: Vec<EF> = Vec::with_capacity(l_0);
                        for k in 0..s_svo_bool {
                            let bit = ((sel_bot >> (s_svo_bool - 1 - k)) & 1) as u32;
                            w_svo.push(if bit == 1 { EF::ONE } else { EF::ZERO });
                        }
                        w_svo.extend_from_slice(&inner_point);
                        let eq_table = eval_eq(&w_svo);
                        let sel_offset = sel_top << l_0;
                        for bsvo in 0..(1 << l_0) {
                            expected[bsvo] += alpha_j * eq_table[bsvo] * EF::from(f[sel_offset + bsvo]);
                        }
                    }
                    assert_eq!(phi, expected, "Phi mismatch at l={l} l_0={l_0} s={s}");
                }
            }
        }
    }

    #[test]
    fn compress_next_claim_matches_brute() {
        let mut rng = StdRng::seed_from_u64(14);
        for l in 4..=7 {
            for l_0 in 1..=(l / 2).min(3) {
                for s in 0..=(l - l_0) {
                    for _trial in 0..2 {
                        let m = l - s;
                        let inner_point: Vec<EF> = (0..m).map(|_| rng.random::<EF>()).collect();
                        let k = 2.min(1 << s);
                        let mut used = Vec::new();
                        while used.len() < k {
                            let sel = if s == 0 { 0 } else { rng.random_range(0..(1usize << s)) };
                            if !used.contains(&sel) {
                                used.push(sel);
                            }
                        }
                        let alphas: Vec<EF> = (0..k).map(|_| rng.random::<EF>()).collect();
                        let f: Vec<F> = (0..(1 << l)).map(|_| rng.random::<F>()).collect();

                        let groups =
                            compress_next_claim_bucketed::<EF>(Some(&f), None, &used, &inner_point, &alphas, l, l_0, s);
                        assert_eq!(groups.len(), l_0 + 2);

                        // Sum contributions across all emitted sub-groups as Phi_nxt(bsvo).
                        let mut phi_svo = vec![EF::ZERO; 1 << l_0];
                        for g in &groups {
                            let e = eval_eq(&g.w_svo);
                            for i in 0..(1usize << l_0) {
                                phi_svo[i] += e[i] * g.p_bar[i];
                            }
                        }

                        // Brute expected:
                        //   Phi_nxt(bsvo) = sum_j alpha_j * sum_{b in {0,1}^m} nxt(inner_point, b) * f[sel_j, b][bsvo_bits]
                        // where b = (beta_split, bsvo) and the sel_j selects the outer block.
                        let nxt_table = matrix_next_mle_folded(&inner_point);
                        let mut expected = vec![EF::ZERO; 1 << l_0];
                        for (&sel_j, &alpha_j) in used.iter().zip(alphas.iter()) {
                            for bsvo in 0..(1usize << l_0) {
                                let mut acc = EF::ZERO;
                                for b in 0..(1usize << m) {
                                    // b encodes (beta_split, bsvo_index) big-endian: high m-l_0
                                    // bits = beta_split, low l_0 bits = bsvo_index. We want
                                    // fixed bsvo, so only b whose low l_0 bits == bsvo.
                                    if (b & ((1usize << l_0) - 1)) != bsvo {
                                        continue;
                                    }
                                    let nxt_val = nxt_table[b];
                                    let f_idx = (sel_j << m) + b;
                                    acc += nxt_val * f[f_idx];
                                }
                                expected[bsvo] += alpha_j * acc;
                            }
                        }
                        assert_eq!(phi_svo, expected, "Phi_nxt mismatch at l={l} l_0={l_0} s={s}");
                    }
                }
            }
        }
    }
}
