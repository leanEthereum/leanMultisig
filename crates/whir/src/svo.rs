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
