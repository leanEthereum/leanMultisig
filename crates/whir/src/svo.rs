#![allow(clippy::needless_range_loop)]
use field::{BasedVectorSpace, ExtensionField, Field, PackedFieldExtension, PackedValue, PrimeCharacteristicRing};
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

pub(crate) fn lagrange_tensor_extend<EF: Field>(out: &mut Vec<EF>, c: EF) {
    // Lagrange basis at `c` for the evaluation set {0, 1, ∞}: L_0 = 1 - c, L_1 = c, L_∞ = c(c - 1).
    let l0 = EF::ONE - c;
    let l_inf = c * (c - EF::ONE);
    *out = out.iter().flat_map(|&v| [v * l0, v * c, v * l_inf]).collect();
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
    debug_assert_eq!(EF::DIMENSION, 5);

    EFPacking::<EF>::to_ext_iter(reduce_svo_rows_one_inner::<EF, 5>(
        rows_packed,
        eq_lo,
        eq_hi,
        sel_off_p,
        stride,
        n_lo,
        svo_len_p,
    ))
}

#[inline]
fn reduce_svo_rows_one_inner<EF, const D: usize>(
    rows_packed: &[PFPacking<EF>],
    eq_lo: &[EF],
    eq_hi: &[EF],
    sel_off_p: usize,
    stride: usize,
    n_lo: usize,
    svo_len_p: usize,
) -> Vec<EFPacking<EF>>
where
    EF: ExtensionField<PF<EF>>,
{
    const SVO_DOT_CHUNK: usize = 4;
    debug_assert_eq!(EF::DIMENSION, D);

    let mut cs: [Vec<PFPacking<EF>>; D] = core::array::from_fn(|_| Vec::with_capacity(stride));
    for &e_hi in eq_hi.iter() {
        let coefs = e_hi.as_basis_coefficients_slice();
        for (d, c) in cs.iter_mut().enumerate() {
            c.push(PFPacking::<EF>::from(coefs[d]));
        }
    }

    let zero = || vec![EFPacking::<EF>::ZERO; svo_len_p];
    let step = |mut acc: Vec<EFPacking<EF>>, b_lo: usize| {
        let base = b_lo * stride;

        let mut tmp_basis = vec![PFPacking::<EF>::ZERO; D * svo_len_p];

        let mut b_hi = 0;
        while b_hi + SVO_DOT_CHUNK <= stride {
            let lhs: [[PFPacking<EF>; SVO_DOT_CHUNK]; D] =
                core::array::from_fn(|d| core::array::from_fn(|i| cs[d][b_hi + i]));

            for k in 0..svo_len_p {
                let row_off = sel_off_p + (base + b_hi) * svo_len_p + k;
                let rhs: [PFPacking<EF>; SVO_DOT_CHUNK] =
                    core::array::from_fn(|i| rows_packed[row_off + i * svo_len_p]);
                for d in 0..D {
                    tmp_basis[d * svo_len_p + k] += PFPacking::<EF>::dot_product::<SVO_DOT_CHUNK>(&lhs[d], &rhs);
                }
            }
            b_hi += SVO_DOT_CHUNK;
        }
        while b_hi < stride {
            let row_off = sel_off_p + (base + b_hi) * svo_len_p;
            for k in 0..svo_len_p {
                let r = rows_packed[row_off + k];
                for d in 0..D {
                    tmp_basis[d * svo_len_p + k] += cs[d][b_hi] * r;
                }
            }
            b_hi += 1;
        }

        let e_lo = EFPacking::<EF>::from(eq_lo[b_lo]);
        for k in 0..svo_len_p {
            let tmp_k = EFPacking::<EF>::from_basis_coefficients_fn(|d| tmp_basis[d * svo_len_p + k]);
            acc[k] += e_lo * tmp_k;
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
    if total_work < PARALLEL_THRESHOLD {
        (0..n_lo).fold(zero(), step)
    } else {
        (0..n_lo).into_par_iter().fold(zero, step).reduce(zero, merge)
    }
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
        out.push(CompressedGroup {
            w_svo: w,
            p_bar: p_eq.iter().map(|v| *v * cp).collect(),
        });
    }
    out.push(CompressedGroup {
        w_svo: vec![EF::ONE; l_0],
        p_bar: s_omega.into_iter().map(|v| v * c_omega).collect(),
    });
    debug_assert_eq!(out.len(), l_0 + 2);
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
            prefix = prefix.iter().flat_map(|&v| [v * one_minus, v * p_j]).collect();
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

        grid_expand_into(&q, big_l, &mut tilde_q, &mut scratch_q);
        grid_expand_into(&e_buf, big_l, &mut tilde_e, &mut scratch_e);

        // Keep only the x_{big_l-1}=0 face (indices 3j) and x_{big_l-1}=∞ face (indices 3j+2).
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
    debug_assert_eq!(lagrange.len(), 3_usize.pow(r as u32));
    let group_reduce = |acc: &AccGroup<EF>| {
        lagrange
            .iter()
            .zip(&acc.acc_0[r])
            .zip(&acc.acc_inf[r])
            .fold((EF::ZERO, EF::ZERO), |(c0, c2), ((&l, &a0), &ainf)| {
                (c0 + l * a0, c2 + l * ainf)
            })
    };
    let add2 = |(a0, a2), (b0, b2)| (a0 + b0, a2 + b2);
    if 2 * lagrange.len() * accs.len() < PARALLEL_THRESHOLD {
        accs.iter().map(group_reduce).fold((EF::ZERO, EF::ZERO), add2)
    } else {
        accs.par_iter().map(group_reduce).reduce(|| (EF::ZERO, EF::ZERO), add2)
    }
}
