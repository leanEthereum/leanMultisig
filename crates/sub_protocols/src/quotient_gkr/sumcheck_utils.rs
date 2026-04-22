use std::borrow::Cow;

use backend::*;

use crate::quotient_gkr::layers::unpack_and_unreverse_active;

#[derive(Clone, Copy, Default)]
struct RoundCoeffs<EF: ExtensionField<PF<EF>>> {
    c0_den: EFPacking<EF>,
    c2_den: EFPacking<EF>,
    c0_num: EFPacking<EF>,
    c2_num: EFPacking<EF>,
}

impl<EF: ExtensionField<PF<EF>>> RoundCoeffs<EF> {
    fn zero() -> Self {
        Self::default()
    }

    fn add_assign_scaled(&mut self, other: Self, w: EFPacking<EF>) {
        self.c0_den += other.c0_den * w;
        self.c2_den += other.c2_den * w;
        self.c0_num += other.c0_num * w;
        self.c2_num += other.c2_num * w;
    }

    fn add_assign_scaled_ef(&mut self, other: Self, w: EF) {
        self.c0_den += other.c0_den * w;
        self.c2_den += other.c2_den * w;
        self.c0_num += other.c0_num * w;
        self.c2_num += other.c2_num * w;
    }

    fn add_assign(&mut self, other: Self) {
        self.c0_den += other.c0_den;
        self.c2_den += other.c2_den;
        self.c0_num += other.c0_num;
        self.c2_num += other.c2_num;
    }
}

#[inline(always)]
fn pair_coeffs_packed<EF, N>(
    nl: (N, N),
    nr: (N, N),
    dl: (EFPacking<EF>, EFPacking<EF>),
    dr: (EFPacking<EF>, EFPacking<EF>),
) -> RoundCoeffs<EF>
where
    EF: ExtensionField<PF<EF>>,
    N: PrimeCharacteristicRing + Copy,
    EFPacking<EF>: Algebra<N>,
{
    let (c0_den, c2_den) = sumcheck_quadratic(((&dl.0, &dl.1), (&dr.0, &dr.1)));
    let (c0_a, c2_a) = sumcheck_quadratic(((&nl.0, &nl.1), (&dr.0, &dr.1)));
    let (c0_b, c2_b) = sumcheck_quadratic(((&nr.0, &nr.1), (&dl.0, &dl.1)));
    RoundCoeffs {
        c0_den,
        c2_den,
        c0_num: c0_a + c0_b,
        c2_num: c2_a + c2_b,
    }
}

#[inline(always)]
fn pair_coeffs_scalar<EF: ExtensionField<PF<EF>>>(
    nl: (EF, EF),
    nr: (EF, EF),
    dl: (EF, EF),
    dr: (EF, EF),
) -> (EF, EF, EF, EF) {
    let (c0_den, c2_den) = sumcheck_quadratic(((&dl.0, &dl.1), (&dr.0, &dr.1)));
    let (c0_a, c2_a) = sumcheck_quadratic(((&nl.0, &nl.1), (&dr.0, &dr.1)));
    let (c0_b, c2_b) = sumcheck_quadratic(((&nr.0, &nr.1), (&dl.0, &dl.1)));
    (c0_den, c2_den, c0_a + c0_b, c2_a + c2_b)
}

#[inline(always)]
fn within_pt<EF: Copy>(remaining_eq: &[EF], head_len: usize) -> Vec<EF> {
    remaining_eq[head_len..remaining_eq.len() - 1]
        .iter()
        .rev()
        .copied()
        .collect()
}

fn finalize_round<EF: ExtensionField<PF<EF>>>(
    prover_state: &mut impl FSProver<EF>,
    coeffs: RoundCoeffs<EF>,
    alpha: EF,
    eq_alpha: EF,
    sum: &mut EF,
    mmf: &mut EF,
    padding_correction: EF,
) -> EF {
    let c0_raw: EF =
        EFPacking::<EF>::to_ext_iter([coeffs.c0_num + coeffs.c0_den * alpha]).sum::<EF>() + padding_correction;
    let c2_raw: EF = EFPacking::<EF>::to_ext_iter([coeffs.c2_num + coeffs.c2_den * alpha]).sum();
    let bare = build_bare_from_coeffs(c0_raw, c2_raw, eq_alpha, *sum, *mmf);
    prover_state.add_sumcheck_polynomial(&bare.coeffs, Some(eq_alpha));
    let r = prover_state.sample();
    let eq_eval = (EF::ONE - eq_alpha) * (EF::ONE - r) + eq_alpha * r;
    *sum = eq_eval * bare.evaluate(r);
    *mmf *= eq_eval;
    r
}

#[allow(clippy::too_many_arguments)]
pub(super) fn quotient_sumcheck_prove_packed_br_base<EF: ExtensionField<PF<EF>>>(
    prover_state: &mut impl FSProver<EF>,
    packed_nums: &[PFPacking<EF>],
    packed_dens: &[EFPacking<EF>],
    parent_chunk_log: usize,
    eq_point: &[EF],
    alpha: EF,
    expected_sum: EF,
) -> (Vec<EF>, [EF; 4]) {
    let w = packing_log_width::<EF>();
    debug_assert!(parent_chunk_log >= w + 3);
    debug_assert_eq!(packed_nums.len(), packed_dens.len());
    let active_chunks = (packed_nums.len() << w) >> parent_chunk_log;

    let k = eq_point.len();
    let mut remaining_eq = eq_point.to_vec();
    let head_len = (k + 1).saturating_sub(parent_chunk_log);
    let mut q_natural = vec![];
    let mut mmf = EF::ONE;
    let mut sum = expected_sum;

    let outer_point: Vec<EF> = remaining_eq[..head_len].to_vec();
    let eq_outer: Vec<EF> = if head_len == 0 {
        vec![EF::ONE]
    } else {
        eval_eq(&outer_point)
    };

    let has_padding = active_chunks < 1usize << head_len;
    let padding_sum = if has_padding {
        alpha * evaluate_mle_of_zero_then_ones(active_chunks, &outer_point)
    } else {
        EF::ZERO
    };

    let eq_alpha_0 = *remaining_eq.last().unwrap();
    let eq_within_0 = eval_eq_packed(&within_pt(&remaining_eq, head_len));
    let coeffs_0 = compute_round_packed::<EF, _>(packed_nums, packed_dens, parent_chunk_log, &eq_outer, &eq_within_0);
    let r0 = finalize_round(
        prover_state,
        coeffs_0,
        alpha,
        eq_alpha_0,
        &mut sum,
        &mut mmf,
        padding_sum,
    );
    q_natural.push(r0);
    remaining_eq.pop();

    let eq_alpha_1 = *remaining_eq.last().unwrap();
    let eq_within_1 = eval_eq_packed(&within_pt(&remaining_eq, head_len));
    let (nums_ext, dens_ext, coeffs_1) =
        fold_and_compute_round_packed::<EF, _>(packed_nums, packed_dens, parent_chunk_log, r0, &eq_outer, &eq_within_1);
    let r1 = finalize_round(
        prover_state,
        coeffs_1,
        alpha,
        eq_alpha_1,
        &mut sum,
        &mut mmf,
        padding_sum,
    );
    q_natural.push(r1);
    remaining_eq.pop();

    run_phase1_sumcheck(
        prover_state,
        Cow::Owned(nums_ext),
        Cow::Owned(dens_ext),
        parent_chunk_log - 2,
        remaining_eq,
        q_natural,
        alpha,
        sum,
        mmf,
        Some(eq_outer),
        Some(r1),
    )
}

/// bit-reversed by chunk + Packed
#[allow(clippy::too_many_arguments)]
pub(super) fn run_phase1_sumcheck<'a, EF: ExtensionField<PF<EF>>>(
    prover_state: &mut impl FSProver<EF>,
    mut nums: Cow<'a, [EFPacking<EF>]>,
    mut dens: Cow<'a, [EFPacking<EF>]>,
    mut layer_chunk_log: usize,
    mut remaining_eq: Vec<EF>,
    mut q_natural: Vec<EF>,
    alpha: EF,
    mut sum: EF,
    mut mmf: EF,
    precomputed_eq_outer: Option<Vec<EF>>,
    initial_pending_r: Option<EF>,
) -> (Vec<EF>, [EF; 4]) {
    let w = packing_log_width::<EF>();
    let head_len = (remaining_eq.len() + 1).saturating_sub(layer_chunk_log);
    let outer_point: Vec<EF> = remaining_eq[..head_len].to_vec();
    let eq_outer: Vec<EF> = precomputed_eq_outer.unwrap_or_else(|| {
        if head_len == 0 {
            vec![EF::ONE]
        } else {
            eval_eq(&outer_point)
        }
    });

    let active_chunks = (nums.len() << w) >> (layer_chunk_log + usize::from(initial_pending_r.is_some()));

    let has_padding = active_chunks < 1usize << head_len;
    let padding_sum = if has_padding {
        alpha * evaluate_mle_of_zero_then_ones(active_chunks, &outer_point)
    } else {
        EF::ZERO
    };

    let mut pending_r: Option<EF> = initial_pending_r;
    while layer_chunk_log > w + 1 && remaining_eq.len() > w + 1 {
        let eq_alpha = *remaining_eq.last().unwrap();
        let eq_within = eval_eq_packed(&within_pt(&remaining_eq, head_len));

        let coeffs = if let Some(prev_r) = pending_r.take() {
            let (new_nums, new_dens, c) = fold_and_compute_round_packed::<EF, _>(
                nums.as_ref(),
                dens.as_ref(),
                layer_chunk_log + 1,
                prev_r,
                &eq_outer,
                &eq_within,
            );
            nums = Cow::Owned(new_nums);
            dens = Cow::Owned(new_dens);
            c
        } else {
            compute_round_packed::<EF, _>(nums.as_ref(), dens.as_ref(), layer_chunk_log, &eq_outer, &eq_within)
        };

        let r = finalize_round(prover_state, coeffs, alpha, eq_alpha, &mut sum, &mut mmf, padding_sum);
        pending_r = Some(r);
        layer_chunk_log -= 1;
        q_natural.push(r);
        remaining_eq.pop();
    }

    if let Some(prev_r) = pending_r {
        let prev_bit = layer_chunk_log - 1 - w;
        let mul = |x: EFPacking<EF>, a: EF| x * a;
        nums = Cow::Owned(fold_multilinear_at_bit(nums.as_ref(), prev_r, prev_bit, &mul));
        dens = Cow::Owned(fold_multilinear_at_bit(dens.as_ref(), prev_r, prev_bit, &mul));
    }

    let nums_nat = unpack_and_unreverse_active::<EF>(nums.as_ref(), layer_chunk_log);
    let dens_nat = unpack_and_unreverse_active::<EF>(dens.as_ref(), layer_chunk_log);
    let num_l: Vec<EF> = nums_nat.iter().step_by(2).copied().collect();
    let num_r: Vec<EF> = nums_nat.iter().skip(1).step_by(2).copied().collect();
    let den_l: Vec<EF> = dens_nat.iter().step_by(2).copied().collect();
    let den_r: Vec<EF> = dens_nat.iter().skip(1).step_by(2).copied().collect();
    run_phase2_sumcheck(
        prover_state,
        num_l,
        num_r,
        den_l,
        den_r,
        remaining_eq,
        q_natural,
        alpha,
        sum,
        mmf,
    )
}

/// Sumcheck over natural-ordered, unpacked data. Terminal phase — applies the
/// single `reverse()` on `q_natural` before returning, undoing the `push()`
/// ordering used throughout both phases.
#[allow(clippy::too_many_arguments)]
pub(super) fn run_phase2_sumcheck<EF: ExtensionField<PF<EF>>>(
    prover_state: &mut impl FSProver<EF>,
    mut num_l: Vec<EF>,
    mut num_r: Vec<EF>,
    mut den_l: Vec<EF>,
    mut den_r: Vec<EF>,
    mut remaining_eq: Vec<EF>,
    mut q_natural: Vec<EF>,
    alpha: EF,
    mut sum: EF,
    mut mmf: EF,
) -> (Vec<EF>, [EF; 4]) {
    for _round in 0..remaining_eq.len() {
        let eq_alpha = *remaining_eq.last().unwrap();
        let eq_prefix = &remaining_eq[..remaining_eq.len() - 1];
        let eq_table = eval_eq(eq_prefix);

        let active_l = num_l.len();
        let active_r = num_r.len();
        let half = eq_table.len();
        let active_pairs = active_l.div_ceil(2);
        let fully_active = active_r / 2;

        let mut c0_den_raw = EF::ZERO;
        let mut c2_den_raw = EF::ZERO;
        let mut c0_num_raw = EF::ZERO;
        let mut c2_num_raw = EF::ZERO;

        for j in 0..fully_active {
            let (c0_den, c2_den, c0_num, c2_num) = pair_coeffs_scalar::<EF>(
                (num_l[2 * j], num_l[2 * j + 1]),
                (num_r[2 * j], num_r[2 * j + 1]),
                (den_l[2 * j], den_l[2 * j + 1]),
                (den_r[2 * j], den_r[2 * j + 1]),
            );
            let eq = eq_table[j];
            c0_den_raw += eq * c0_den;
            c2_den_raw += eq * c2_den;
            c0_num_raw += eq * c0_num;
            c2_num_raw += eq * c2_num;
        }
        // Boundary
        let pair = |arr: &[EF], idx: usize, pad: EF| {
            (
                arr.get(idx).copied().unwrap_or(pad),
                arr.get(idx + 1).copied().unwrap_or(pad),
            )
        };
        #[allow(clippy::needless_range_loop)]
        for j in fully_active..active_pairs {
            let (c0_den, c2_den, c0_num, c2_num) = pair_coeffs_scalar::<EF>(
                pair(&num_l, 2 * j, EF::ZERO),
                pair(&num_r, 2 * j, EF::ZERO),
                pair(&den_l, 2 * j, EF::ONE),
                pair(&den_r, 2 * j, EF::ONE),
            );
            let eq = eq_table[j];
            c0_den_raw += eq * c0_den;
            c2_den_raw += eq * c2_den;
            c0_num_raw += eq * c0_num;
            c2_num_raw += eq * c2_num;
        }

        let padding_sum = if active_pairs < half {
            alpha * evaluate_mle_of_zero_then_ones(active_pairs, eq_prefix)
        } else {
            EF::ZERO
        };

        let bare = build_bare_from_coeffs(
            c0_num_raw + alpha * c0_den_raw + padding_sum,
            c2_num_raw + alpha * c2_den_raw,
            eq_alpha,
            sum,
            mmf,
        );

        prover_state.add_sumcheck_polynomial(&bare.coeffs, Some(eq_alpha));
        let r = prover_state.sample();
        let eq_eval = (EF::ONE - eq_alpha) * (EF::ONE - r) + eq_alpha * r;
        sum = eq_eval * bare.evaluate(r);
        mmf *= eq_eval;

        num_l = fold_normal_with_padding(&num_l, r, EF::ZERO);
        num_r = fold_normal_with_padding(&num_r, r, EF::ZERO);
        den_l = fold_normal_with_padding(&den_l, r, EF::ONE);
        den_r = fold_normal_with_padding(&den_r, r, EF::ONE);

        q_natural.push(r);
        remaining_eq.pop();
    }

    q_natural.reverse();
    let evals = [num_l[0], num_r[0], den_l[0], den_r[0]];
    (q_natural, evals)
}

fn fold_normal_with_padding<EF: ExtensionField<PF<EF>>>(m: &[EF], r: EF, pad_value: EF) -> Vec<EF> {
    let active = m.len();
    let new_active = active.div_ceil(2);
    assert!(new_active != 0);
    let mut out: Vec<EF> = unsafe { uninitialized_vec(new_active) };

    let compute = |(i, slot): (usize, &mut EF)| {
        let a = m[2 * i];
        let b = if 2 * i + 1 < active { m[2 * i + 1] } else { pad_value };
        *slot = a + (b - a) * r;
    };

    if new_active < PARALLEL_THRESHOLD {
        out.iter_mut().enumerate().for_each(compute);
    } else {
        out.par_iter_mut()
            .with_min_len(PARALLEL_THRESHOLD)
            .enumerate()
            .for_each(compute);
    }
    out
}

fn compute_round_packed<EF: ExtensionField<PF<EF>>, N>(
    nums: &[N],
    dens: &[EFPacking<EF>],
    layer_chunk_log: usize,
    eq_outer: &[EF],
    eq_within: &[EFPacking<EF>],
) -> RoundCoeffs<EF>
where
    N: PrimeCharacteristicRing + Copy + Send + Sync,
    EFPacking<EF>: Algebra<N>,
{
    let w = packing_log_width::<EF>();
    debug_assert!(layer_chunk_log >= w + 2);
    let layer_packed = 1usize << (layer_chunk_log - w);
    let half = layer_packed / 2;
    let quarter = layer_packed / 4;
    debug_assert!(nums.len().is_multiple_of(layer_packed));
    debug_assert_eq!(dens.len(), nums.len());
    debug_assert_eq!(eq_within.len(), quarter);

    nums.par_chunks_exact(layer_packed)
        .zip(dens.par_chunks_exact(layer_packed))
        .enumerate()
        .fold(RoundCoeffs::<EF>::zero, |mut acc, (c, (n_c, d_c))| {
            let eq_o: EF = eq_outer.get(c).copied().unwrap_or(EF::ONE);
            let mut local = RoundCoeffs::<EF>::zero();
            for inner in 0..quarter {
                let coeffs = pair_coeffs_packed::<EF, _>(
                    (n_c[inner], n_c[inner + quarter]),
                    (n_c[inner + half], n_c[inner + half + quarter]),
                    (d_c[inner], d_c[inner + quarter]),
                    (d_c[inner + half], d_c[inner + half + quarter]),
                );
                local.add_assign_scaled(coeffs, eq_within[inner]);
            }
            acc.add_assign_scaled_ef(local, eq_o);
            acc
        })
        .reduce(RoundCoeffs::<EF>::zero, |a, b| {
            let mut r = a;
            r.add_assign(b);
            r
        })
}

#[allow(clippy::type_complexity)]
fn fold_and_compute_round_packed<EF: ExtensionField<PF<EF>>, N>(
    nums: &[N],
    dens: &[EFPacking<EF>],
    layer_chunk_log_old: usize,
    prev_r: EF,
    eq_outer: &[EF],
    eq_within: &[EFPacking<EF>],
) -> (Vec<EFPacking<EF>>, Vec<EFPacking<EF>>, RoundCoeffs<EF>)
where
    N: PrimeCharacteristicRing + Copy + Send + Sync,
    EFPacking<EF>: Algebra<N>,
{
    let w = packing_log_width::<EF>();
    debug_assert!(layer_chunk_log_old >= w + 3);
    let in_packed = 1usize << (layer_chunk_log_old - w);
    let in_half = in_packed / 2;
    let in_quarter = in_packed / 4;
    let in_eighth = in_packed / 8;
    let out_packed = in_packed / 2;
    let out_half = out_packed / 2;
    let out_quarter = out_packed / 4;
    debug_assert!(nums.len().is_multiple_of(in_packed));
    debug_assert_eq!(dens.len(), nums.len());
    debug_assert_eq!(eq_within.len(), in_eighth);

    let active_out_packed = nums.len() / 2;
    let mut new_nums: Vec<EFPacking<EF>> = unsafe { uninitialized_vec(active_out_packed) };
    let mut new_dens: Vec<EFPacking<EF>> = unsafe { uninitialized_vec(active_out_packed) };
    let prev_r_packed: EFPacking<EF> = <EFPacking<EF> as From<EF>>::from(prev_r);

    let coeffs = nums
        .par_chunks_exact(in_packed)
        .zip(dens.par_chunks_exact(in_packed))
        .zip(new_nums.par_chunks_exact_mut(out_packed))
        .zip(new_dens.par_chunks_exact_mut(out_packed))
        .enumerate()
        .fold(RoundCoeffs::<EF>::zero, |mut acc, (c, (((n_c, d_c), nn_c), nd_c))| {
            let eq_o: EF = eq_outer.get(c).copied().unwrap_or(EF::ONE);
            let mut local = RoundCoeffs::<EF>::zero();
            for i in 0..in_eighth {
                let l_p0_c0 = i;
                let l_p0_c1 = i + in_eighth;
                let l_p1_c0 = i + in_quarter;
                let l_p1_c1 = i + in_quarter + in_eighth;
                let r_p0_c0 = i + in_half;
                let r_p0_c1 = i + in_half + in_eighth;
                let r_p1_c0 = i + in_half + in_quarter;
                let r_p1_c1 = i + in_half + in_quarter + in_eighth;

                let fl_nl = prev_r_packed * (n_c[l_p1_c0] - n_c[l_p0_c0]) + n_c[l_p0_c0];
                let fr_nl = prev_r_packed * (n_c[l_p1_c1] - n_c[l_p0_c1]) + n_c[l_p0_c1];
                let fl_nr = prev_r_packed * (n_c[r_p1_c0] - n_c[r_p0_c0]) + n_c[r_p0_c0];
                let fr_nr = prev_r_packed * (n_c[r_p1_c1] - n_c[r_p0_c1]) + n_c[r_p0_c1];
                let fl_dl = d_c[l_p0_c0] + (d_c[l_p1_c0] - d_c[l_p0_c0]) * prev_r;
                let fr_dl = d_c[l_p0_c1] + (d_c[l_p1_c1] - d_c[l_p0_c1]) * prev_r;
                let fl_dr = d_c[r_p0_c0] + (d_c[r_p1_c0] - d_c[r_p0_c0]) * prev_r;
                let fr_dr = d_c[r_p0_c1] + (d_c[r_p1_c1] - d_c[r_p0_c1]) * prev_r;

                nn_c[i] = fl_nl;
                nn_c[i + out_quarter] = fr_nl;
                nn_c[i + out_half] = fl_nr;
                nn_c[i + out_half + out_quarter] = fr_nr;
                nd_c[i] = fl_dl;
                nd_c[i + out_quarter] = fr_dl;
                nd_c[i + out_half] = fl_dr;
                nd_c[i + out_half + out_quarter] = fr_dr;

                let round = pair_coeffs_packed::<EF, EFPacking<EF>>(
                    (fl_nl, fr_nl),
                    (fl_nr, fr_nr),
                    (fl_dl, fr_dl),
                    (fl_dr, fr_dr),
                );
                local.add_assign_scaled(round, eq_within[i]);
            }
            acc.add_assign_scaled_ef(local, eq_o);
            acc
        })
        .reduce(RoundCoeffs::<EF>::zero, |a, b| {
            let mut r = a;
            r.add_assign(b);
            r
        });

    (new_nums, new_dens, coeffs)
}

fn build_bare_from_coeffs<EF: ExtensionField<PF<EF>>>(
    c0_raw: EF,
    c2_raw: EF,
    eq_alpha: EF,
    sum: EF,
    mmf: EF,
) -> DensePolynomial<EF> {
    let c0_mmf = c0_raw * mmf;
    let c2_mmf = c2_raw * mmf;
    let h1_mmf = (sum - (EF::ONE - eq_alpha) * c0_mmf) / eq_alpha;
    let c1_mmf = h1_mmf - c0_mmf - c2_mmf;
    DensePolynomial::new(vec![c0_mmf, c1_mmf, c2_mmf])
}
