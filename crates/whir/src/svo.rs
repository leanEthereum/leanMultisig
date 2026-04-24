#![allow(clippy::needless_range_loop)]
use field::{ExtensionField, Field, PackedFieldExtension, PackedValue, PrimeCharacteristicRing};
use poly::{EFPacking, PARALLEL_THRESHOLD, PF, PFPacking, compute_eval_eq, eval_eq, packing_log_width};
use rayon::prelude::*;

#[derive(Debug, Clone)]
pub(crate) struct CompressedGroup<EF> {
    pub(crate) w_svo: Vec<EF>,
    pub(crate) p_bar: Vec<EF>,
}

#[derive(Debug)]
pub(crate) struct AccGroup<EF> {
    pub(crate) acc_0: Vec<Vec<EF>>,
    pub(crate) acc_inf: Vec<Vec<EF>>,
}

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
                out_block[3 * j + 2] = f1 - f0;
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

fn round_fill_l1<EF: Field>(q: &[EF], e: &[EF]) -> (Vec<EF>, Vec<EF>) {
    debug_assert_eq!(q.len(), 2);
    debug_assert_eq!(e.len(), 2);
    let q_inf = q[1] - q[0];
    let e_inf = e[1] - e[0];
    (vec![q[0] * e[0]], vec![q_inf * e_inf])
}

fn round_fill_l2<EF: Field>(q: &[EF], e: &[EF]) -> (Vec<EF>, Vec<EF>) {
    debug_assert_eq!(q.len(), 4);
    debug_assert_eq!(e.len(), 4);

    // x_1 = 0 face: directly from Boolean evals.
    let q_00 = q[0];
    let q_10 = q[1];
    let q_i0 = q[1] - q[0];
    let e_00 = e[0];
    let e_10 = e[1];
    let e_i0 = e[1] - e[0];

    // x_1 = ∞ face: q(x_0, x_1=∞) = q(x_0, 1) - q(x_0, 0).
    let q_0i = q[2] - q[0];
    let q_1i = q[3] - q[1];
    let q_ii = q_1i - q_0i;
    let e_0i = e[2] - e[0];
    let e_1i = e[3] - e[1];
    let e_ii = e_1i - e_0i;

    (
        vec![q_00 * e_00, q_10 * e_10, q_i0 * e_i0],
        vec![q_0i * e_0i, q_1i * e_1i, q_ii * e_ii],
    )
}

fn round_fill_l3<EF: Field>(q: &[EF], e: &[EF]) -> (Vec<EF>, Vec<EF>) {
    debug_assert_eq!(q.len(), 8);
    debug_assert_eq!(e.len(), 8);

    // x_2 = 0 slice extended over (x_0, x_1) ∈ {0,1,∞}^2.
    let q_000 = q[0];
    let q_100 = q[1];
    let q_010 = q[2];
    let q_110 = q[3];
    let q_i00 = q_100 - q_000;
    let q_i10 = q_110 - q_010;
    let q_0i0 = q_010 - q_000;
    let q_1i0 = q_110 - q_100;
    let q_ii0 = q_i10 - q_i00;

    let e_000 = e[0];
    let e_100 = e[1];
    let e_010 = e[2];
    let e_110 = e[3];
    let e_i00 = e_100 - e_000;
    let e_i10 = e_110 - e_010;
    let e_0i0 = e_010 - e_000;
    let e_1i0 = e_110 - e_100;
    let e_ii0 = e_i10 - e_i00;

    // x_2 = 1 slice (needed only to form x_2 = ∞).
    let q_001 = q[4];
    let q_101 = q[5];
    let q_011 = q[6];
    let q_111 = q[7];
    let q_i01 = q_101 - q_001;
    let q_i11 = q_111 - q_011;
    let q_0i1 = q_011 - q_001;
    let q_1i1 = q_111 - q_101;
    let q_ii1 = q_i11 - q_i01;

    let e_001 = e[4];
    let e_101 = e[5];
    let e_011 = e[6];
    let e_111 = e[7];
    let e_i01 = e_101 - e_001;
    let e_i11 = e_111 - e_011;
    let e_0i1 = e_011 - e_001;
    let e_1i1 = e_111 - e_101;
    let e_ii1 = e_i11 - e_i01;

    // x_2 = ∞ slice: extrapolate `(..)_1 - (..)_0` pointwise.
    let q_00i = q_001 - q_000;
    let q_10i = q_101 - q_100;
    let q_01i = q_011 - q_010;
    let q_11i = q_111 - q_110;
    let q_i0i = q_i01 - q_i00;
    let q_i1i = q_i11 - q_i10;
    let q_0ii = q_0i1 - q_0i0;
    let q_1ii = q_1i1 - q_1i0;
    let q_iii = q_ii1 - q_ii0;

    let e_00i = e_001 - e_000;
    let e_10i = e_101 - e_100;
    let e_01i = e_011 - e_010;
    let e_11i = e_111 - e_110;
    let e_i0i = e_i01 - e_i00;
    let e_i1i = e_i11 - e_i10;
    let e_0ii = e_0i1 - e_0i0;
    let e_1ii = e_1i1 - e_1i0;
    let e_iii = e_ii1 - e_ii0;

    // Output order: j = 3*x_0 + x_1; within each x_0 group, x_1 in {0, 1, ∞}.
    (
        vec![
            q_000 * e_000,
            q_010 * e_010,
            q_0i0 * e_0i0,
            q_100 * e_100,
            q_110 * e_110,
            q_1i0 * e_1i0,
            q_i00 * e_i00,
            q_i10 * e_i10,
            q_ii0 * e_ii0,
        ],
        vec![
            q_00i * e_00i,
            q_01i * e_01i,
            q_0ii * e_0ii,
            q_10i * e_10i,
            q_11i * e_11i,
            q_1ii * e_1ii,
            q_i0i * e_i0i,
            q_i1i * e_i1i,
            q_iii * e_iii,
        ],
    )
}

pub(crate) fn lagrange_tensor_extend<EF: Field>(out: &mut Vec<EF>, c: EF) {
    // Lagrange basis at `c` for the evaluation set {0, 1, ∞}:
    //   L_0(c)   = 1 - c
    //   L_1(c)   = c
    //   L_∞(c)   = c (c - 1)
    let l0 = EF::ONE - c;
    let l1 = c;
    let l_inf = c * (c - EF::ONE);
    let old_len = out.len();
    out.resize(old_len * 3, EF::ZERO);
    // Walk backwards so writes never overlap unread input.
    for i in (0..old_len).rev() {
        let v = out[i];
        out[3 * i] = v * l0;
        out[3 * i + 1] = v * l1;
        out[3 * i + 2] = v * l_inf;
    }
}
fn reduce_svo_rows_one<EF>(
    rows: &[PF<EF>],
    eq_lo: &[EF],
    eq_hi: &[EF],
    sel_offset: usize,
    svo_len: usize,
) -> impl IntoIterator<Item = EF>
where
    EF: ExtensionField<PF<EF>>,
{
    let w = packing_log_width::<EF>();
    debug_assert!(svo_len.is_multiple_of(1 << w));
    debug_assert!(sel_offset.is_multiple_of(1 << w));
    debug_assert!(eq_lo.len().is_power_of_two());
    debug_assert!(eq_hi.len().is_power_of_two());

    let rows_packed = PFPacking::<EF>::pack_slice(rows);
    let svo_len_p = svo_len >> w;
    let sel_off_p = sel_offset >> w;
    let n_lo = eq_lo.len();
    let stride = eq_hi.len(); // = 2^m_hi — coefficient of b_lo in the full b index

    let zero = || vec![EFPacking::<EF>::ZERO; svo_len_p];
    let step = |mut acc: Vec<EFPacking<EF>>, b_lo: usize| {
        // Inner reduction against eq_hi → tmp, scaled by eq_lo[b_lo] into acc.
        let base = b_lo * stride;
        let mut tmp = vec![EFPacking::<EF>::ZERO; svo_len_p];
        for b_hi in 0..stride {
            let e_hi = EFPacking::<EF>::from(eq_hi[b_hi]);
            let row_off = sel_off_p + (base + b_hi) * svo_len_p;
            let row = &rows_packed[row_off..][..svo_len_p];
            for k in 0..svo_len_p {
                tmp[k] += e_hi * row[k];
            }
        }
        let e_lo = EFPacking::<EF>::from(eq_lo[b_lo]);
        for k in 0..svo_len_p {
            acc[k] += e_lo * tmp[k];
        }
        acc
    };
    let merge = |mut a: Vec<EFPacking<EF>>, b: Vec<EFPacking<EF>>| {
        for (x, y) in a.iter_mut().zip(&b) {
            *x += *y;
        }
        a
    };
    let total_work = n_lo * stride * svo_len_p;
    let acc_packed = if total_work < PARALLEL_THRESHOLD {
        (0..n_lo).fold(zero(), step)
    } else {
        (0..n_lo).into_par_iter().fold(zero, step).reduce(zero, merge)
    };
    EFPacking::<EF>::to_ext_iter(acc_packed)
}

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

    // Factored eq(p_split, ·): split at the midpoint so storage is
    // `2^⌊m/2⌋ + 2^⌈m/2⌉` instead of `2^m`.
    let m_lo = m_split / 2;
    let eq_lo = eval_eq(&p_split[..m_lo]);
    let eq_hi = eval_eq(&p_split[m_lo..]);
    let svo_len = 1usize << l_0;
    let mut p_bar = vec![EF::ZERO; svo_len];

    for (&sel_j, &alpha_j) in sel_bits.iter().zip(alpha_powers.iter()) {
        let sel_offset = sel_j << (l - s);
        let contrib = reduce_svo_rows_one::<EF>(f, &eq_lo, &eq_hi, sel_offset, svo_len);
        for (p, s) in p_bar.iter_mut().zip(contrib) {
            *p += alpha_j * s;
        }
    }

    CompressedGroup {
        w_svo: p_svo.to_vec(),
        p_bar,
    }
}

pub(crate) fn compress_next_claim<EF>(
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

        let c_base = sel_offset + ((split_len - 1) << l_0);
        for bsvo in 0..svo_len {
            s_omega[bsvo] += alpha_j * f[c_base + bsvo];
        }

        for bsvo in 0..svo_len {
            sigma_split[bsvo] += alpha_j * sig_contrib[bsvo];
            p_eq[bsvo] += alpha_j * eq_contrib[bsvo];
        }
    }

    let mut out: Vec<CompressedGroup<EF>> = Vec::with_capacity(l_0 + 2);
    out.push(CompressedGroup {
        w_svo: vec![EF::ZERO; l_0],
        p_bar: sigma_split,
    });
    for (pivot_pos, &cp) in c_pivot.iter().enumerate() {
        let mut w = vec![EF::ZERO; l_0];
        w[..pivot_pos].copy_from_slice(&inner_point[m_split..m_split + pivot_pos]);
        w[pivot_pos] = EF::ONE;
        let pb: Vec<EF> = p_eq.iter().map(|v| *v * cp).collect();
        out.push(CompressedGroup { w_svo: w, p_bar: pb });
    }
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

fn build_bar_t_split<EF: Field>(p: &[EF], m_split: usize, m: usize) -> (Vec<EF>, EF) {
    let out_len = 1usize << m_split;
    let mut bar_t = vec![EF::ZERO; out_len];

    let mut suf = vec![EF::ONE; m + 1];
    for j in (0..m).rev() {
        suf[j] = suf[j + 1] * p[j];
    }
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

pub(crate) fn build_accumulators_single<EF>(group: &CompressedGroup<EF>, l_0: usize) -> AccGroup<EF>
where
    EF: ExtensionField<PF<EF>>,
{
    assert_eq!(group.w_svo.len(), l_0);
    assert_eq!(group.p_bar.len(), 1 << l_0);

    let mut acc_0: Vec<Vec<EF>> = vec![Vec::new(); l_0];
    let mut acc_inf: Vec<Vec<EF>> = vec![Vec::new(); l_0];

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

        let (a, b) = match big_l {
            1 => round_fill_l1(&q, &e_buf),
            2 => round_fill_l2(&q, &e_buf),
            3 => round_fill_l3(&q, &e_buf),
            _ => {
                grid_expand_into(&q, big_l, &mut tilde_q, &mut scratch_q);
                grid_expand_into(&e_buf, big_l, &mut tilde_e, &mut scratch_e);

                let s = 3_usize.pow(r as u32);
                let mut a = EF::zero_vec(s);
                let mut b = EF::zero_vec(s);
                let fill = |(j, (a_j, b_j)): (usize, (&mut EF, &mut EF))| {
                    *a_j = tilde_q[3 * j] * tilde_e[3 * j];
                    *b_j = tilde_q[3 * j + 2] * tilde_e[3 * j + 2];
                };
                if s < PARALLEL_THRESHOLD {
                    a.iter_mut().zip(b.iter_mut()).enumerate().for_each(fill);
                } else {
                    a.par_iter_mut().zip(b.par_iter_mut()).enumerate().for_each(fill);
                }
                (a, b)
            }
        };
        acc_0[r] = a;
        acc_inf[r] = b;

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
    AccGroup { acc_0, acc_inf }
}

pub(crate) fn build_accumulators<EF>(groups: &[CompressedGroup<EF>], l_0: usize) -> Vec<AccGroup<EF>>
where
    EF: ExtensionField<PF<EF>>,
{
    groups.par_iter().map(|g| build_accumulators_single(g, l_0)).collect()
}

pub(crate) fn round_message_with_tensor<EF: Field>(r: usize, lagrange: &[EF], accs: &[AccGroup<EF>]) -> (EF, EF) {
    let s = 3_usize.pow(r as u32);
    debug_assert_eq!(lagrange.len(), s);

    let total_work = 2 * s * accs.len();
    let group_reduce = |acc: &AccGroup<EF>| -> (EF, EF) {
        debug_assert_eq!(acc.acc_0[r].len(), s);
        debug_assert_eq!(acc.acc_inf[r].len(), s);
        let mut c0 = EF::ZERO;
        let mut c2 = EF::ZERO;
        for j in 0..s {
            let l = lagrange[j];
            c0 += l * acc.acc_0[r][j];
            c2 += l * acc.acc_inf[r][j];
        }
        (c0, c2)
    };
    let add2 = |(a0, a2), (b0, b2)| (a0 + b0, a2 + b2);
    if total_work < PARALLEL_THRESHOLD {
        accs.iter().map(group_reduce).fold((EF::ZERO, EF::ZERO), add2)
    } else {
        accs.par_iter().map(group_reduce).reduce(|| (EF::ZERO, EF::ZERO), add2)
    }
}
