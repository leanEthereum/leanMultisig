use std::borrow::Cow;

use backend::*;

use crate::quotient_gkr::layers::unpack_and_unreverse_active;

#[inline(always)]
fn within_pt<EF: Copy>(remaining_eq: &[EF], head_len: usize) -> Vec<EF> {
    remaining_eq[head_len..remaining_eq.len() - 1]
        .iter()
        .rev()
        .copied()
        .collect()
}

fn packed_padding_correction<EF: ExtensionField<PF<EF>>>(active_chunks: usize, outer_point: &[EF]) -> EF {
    if outer_point.is_empty() {
        debug_assert!(active_chunks <= 1);
        return if active_chunks == 0 { EF::ONE } else { EF::ZERO };
    }
    evaluate_mle_of_zero_then_ones(active_chunks, outer_point)
}

#[allow(clippy::too_many_arguments)]
fn finalize_round<EF: ExtensionField<PF<EF>>>(
    prover_state: &mut impl FSProver<EF>,
    c0_s: EFPacking<EF>,
    c2_s: EFPacking<EF>,
    c0_d: EFPacking<EF>,
    c2_d: EFPacking<EF>,
    alpha: EF,
    eq_alpha: EF,
    sum: &mut EF,
    mmf: &mut EF,
    padding_correction: EF, // added to c0_raw; 0 when no padding
) -> EF {
    let c0_raw: EF = EFPacking::<EF>::to_ext_iter([c0_d + c0_s * alpha]).sum::<EF>() + padding_correction;
    let c2_raw: EF = EFPacking::<EF>::to_ext_iter([c2_d + c2_s * alpha]).sum();
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
    debug_assert!(parent_chunk_log > w + 1);
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

    let padding_sum = alpha * packed_padding_correction::<EF>(active_chunks, &outer_point);
    let has_padding = {
        let total_chunks = 1usize << head_len;
        active_chunks < total_chunks
    };

    let eq_alpha_0 = *remaining_eq.last().unwrap();
    let eq_within_0 = eval_eq_packed(&within_pt(&remaining_eq, head_len));
    let (c0_s, c2_s, c0_d, c2_d) =
        compute_round_packed::<EF, _>(packed_nums, packed_dens, parent_chunk_log, &eq_outer, &eq_within_0);
    let r0 = finalize_round(
        prover_state,
        c0_s,
        c2_s,
        c0_d,
        c2_d,
        alpha,
        eq_alpha_0,
        &mut sum,
        &mut mmf,
        if has_padding { padding_sum } else { EF::ZERO },
    );
    q_natural.insert(0, r0);
    remaining_eq.pop();
    assert!(parent_chunk_log >= w + 3);

    let eq_alpha_1 = *remaining_eq.last().unwrap();
    let eq_within_1 = eval_eq_packed(&within_pt(&remaining_eq, head_len));
    let (nums_ext, dens_ext, c0_s, c2_s, c0_d, c2_d) =
        fold_and_compute_round_packed::<EF, _>(packed_nums, packed_dens, parent_chunk_log, r0, &eq_outer, &eq_within_1);
    let r1 = finalize_round(
        prover_state,
        c0_s,
        c2_s,
        c0_d,
        c2_d,
        alpha,
        eq_alpha_1,
        &mut sum,
        &mut mmf,
        if has_padding { padding_sum } else { EF::ZERO },
    );
    q_natural.insert(0, r1);
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

    let padding_sum = alpha * packed_padding_correction::<EF>(active_chunks, &outer_point);
    let has_padding = {
        let total_chunks = 1usize << head_len;
        active_chunks < total_chunks
    };

    let mut pending_r: Option<EF> = initial_pending_r;
    while layer_chunk_log > w + 1 && remaining_eq.len() > w + 1 {
        let eq_alpha = *remaining_eq.last().unwrap();
        let eq_within = eval_eq_packed(&within_pt(&remaining_eq, head_len));

        let (c0_s, c2_s, c0_d, c2_d) = if let Some(prev_r) = pending_r.take() {
            let (new_nums, new_dens, c0s, c2s, c0d, c2d) = fold_and_compute_round_packed::<EF, _>(
                nums.as_ref(),
                dens.as_ref(),
                layer_chunk_log + 1,
                prev_r,
                &eq_outer,
                &eq_within,
            );
            nums = Cow::Owned(new_nums);
            dens = Cow::Owned(new_dens);
            (c0s, c2s, c0d, c2d)
        } else {
            compute_round_packed::<EF, _>(nums.as_ref(), dens.as_ref(), layer_chunk_log, &eq_outer, &eq_within)
        };

        let r = finalize_round(
            prover_state,
            c0_s,
            c2_s,
            c0_d,
            c2_d,
            alpha,
            eq_alpha,
            &mut sum,
            &mut mmf,
            if has_padding { padding_sum } else { EF::ZERO },
        );
        pending_r = Some(r);
        layer_chunk_log -= 1;
        q_natural.insert(0, r);
        remaining_eq.pop();
    }

    if let Some(prev_r) = pending_r {
        let prev_bit = layer_chunk_log - 1 - w;
        nums = Cow::Owned(fold_ext_active_at_bit::<EF>(
            nums.as_ref(),
            prev_r,
            prev_bit,
            layer_chunk_log + 1,
        ));
        dens = Cow::Owned(fold_ext_active_at_bit::<EF>(
            dens.as_ref(),
            prev_r,
            prev_bit,
            layer_chunk_log + 1,
        ));
    }

    let nums_nat = unpack_and_unreverse_active::<EF>(nums.as_ref(), layer_chunk_log);
    let dens_nat = unpack_and_unreverse_active::<EF>(dens.as_ref(), layer_chunk_log);
    let (num_l, num_r) = even_odd_split(&nums_nat);
    let (den_l, den_r) = even_odd_split(&dens_nat);
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

// Normal ordering (not bit-reversed) + not packed.
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

        let mut c0_s_raw = EF::ZERO;
        let mut c2_s_raw = EF::ZERO;
        let mut c0_d_raw = EF::ZERO;
        let mut c2_d_raw = EF::ZERO;
        let fully_active = active_r / 2;
        for j in 0..fully_active {
            let nl0 = num_l[2 * j];
            let nl1 = num_l[2 * j + 1];
            let nr0 = num_r[2 * j];
            let nr1 = num_r[2 * j + 1];
            let dl0 = den_l[2 * j];
            let dl1 = den_l[2 * j + 1];
            let dr0 = den_r[2 * j];
            let dr1 = den_r[2 * j + 1];
            let (c0_s, c2_s) = sumcheck_quadratic(((&dl0, &dl1), (&dr0, &dr1)));
            let (c0_a, c2_a) = sumcheck_quadratic(((&nl0, &nl1), (&dr0, &dr1)));
            let (c0_b, c2_b) = sumcheck_quadratic(((&nr0, &nr1), (&dl0, &dl1)));
            let eq = eq_table[j];
            c0_s_raw += eq * c0_s;
            c2_s_raw += eq * c2_s;
            c0_d_raw += eq * (c0_a + c0_b);
            c2_d_raw += eq * (c2_a + c2_b);
        }
        // Boundary
        for j in fully_active..active_pairs {
            let nl0 = if 2 * j < active_l { num_l[2 * j] } else { EF::ZERO };
            let nl1 = if 2 * j + 1 < active_l {
                num_l[2 * j + 1]
            } else {
                EF::ZERO
            };
            let nr0 = if 2 * j < active_r { num_r[2 * j] } else { EF::ZERO };
            let nr1 = if 2 * j + 1 < active_r {
                num_r[2 * j + 1]
            } else {
                EF::ZERO
            };
            let dl0 = if 2 * j < active_l { den_l[2 * j] } else { EF::ONE };
            let dl1 = if 2 * j + 1 < active_l {
                den_l[2 * j + 1]
            } else {
                EF::ONE
            };
            let dr0 = if 2 * j < active_r { den_r[2 * j] } else { EF::ONE };
            let dr1 = if 2 * j + 1 < active_r {
                den_r[2 * j + 1]
            } else {
                EF::ONE
            };
            let (c0_s, c2_s) = sumcheck_quadratic(((&dl0, &dl1), (&dr0, &dr1)));
            let (c0_a, c2_a) = sumcheck_quadratic(((&nl0, &nl1), (&dr0, &dr1)));
            let (c0_b, c2_b) = sumcheck_quadratic(((&nr0, &nr1), (&dl0, &dl1)));
            let eq = eq_table[j];
            c0_s_raw += eq * c0_s;
            c2_s_raw += eq * c2_s;
            c0_d_raw += eq * (c0_a + c0_b);
            c2_d_raw += eq * (c2_a + c2_b);
        }

        // Correction
        let padding_sum = if active_pairs < half {
            alpha * evaluate_mle_of_zero_then_ones(active_pairs, eq_prefix)
        } else {
            EF::ZERO
        };

        let bare = build_bare_from_coeffs(
            c0_d_raw + alpha * c0_s_raw + padding_sum,
            c2_d_raw + alpha * c2_s_raw,
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

        q_natural.insert(0, r);
        remaining_eq.pop();
    }

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

type Coeffs4<EF> = (EFPacking<EF>, EFPacking<EF>, EFPacking<EF>, EFPacking<EF>);

fn compute_round_packed<EF: ExtensionField<PF<EF>>, N>(
    nums: &[N],
    dens: &[EFPacking<EF>],
    layer_chunk_log: usize,
    eq_outer: &[EF],
    eq_within: &[EFPacking<EF>],
) -> Coeffs4<EF>
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
        .fold(coeffs4_zero::<EF>, |mut acc, (c, (n_c, d_c))| {
            let eq_o: EF = eq_outer.get(c).copied().unwrap_or(EF::ONE);
            let mut local = coeffs4_zero::<EF>();
            for inner in 0..quarter {
                let nl0 = n_c[inner];
                let nl1 = n_c[inner + quarter];
                let nr0 = n_c[inner + half];
                let nr1 = n_c[inner + half + quarter];
                let dl0 = d_c[inner];
                let dl1 = d_c[inner + quarter];
                let dr0 = d_c[inner + half];
                let dr1 = d_c[inner + half + quarter];

                let (c0_s, c2_s) = sumcheck_quadratic(((&dl0, &dl1), (&dr0, &dr1)));
                let (c0_a, c2_a) = sumcheck_quadratic(((&nl0, &nl1), (&dr0, &dr1)));
                let (c0_b, c2_b) = sumcheck_quadratic(((&nr0, &nr1), (&dl0, &dl1)));
                let eq_w = eq_within[inner];
                local.0 += c0_s * eq_w;
                local.1 += c2_s * eq_w;
                local.2 += (c0_a + c0_b) * eq_w;
                local.3 += (c2_a + c2_b) * eq_w;
            }
            acc.0 += local.0 * eq_o;
            acc.1 += local.1 * eq_o;
            acc.2 += local.2 * eq_o;
            acc.3 += local.3 * eq_o;
            acc
        })
        .reduce(coeffs4_zero::<EF>, coeffs4_add::<EF>)
}

#[inline(always)]
fn coeffs4_zero<EF: ExtensionField<PF<EF>>>() -> Coeffs4<EF> {
    (
        EFPacking::<EF>::ZERO,
        EFPacking::<EF>::ZERO,
        EFPacking::<EF>::ZERO,
        EFPacking::<EF>::ZERO,
    )
}

#[inline(always)]
fn coeffs4_add<EF: ExtensionField<PF<EF>>>(a: Coeffs4<EF>, b: Coeffs4<EF>) -> Coeffs4<EF> {
    (a.0 + b.0, a.1 + b.1, a.2 + b.2, a.3 + b.3)
}

#[allow(clippy::type_complexity)]
fn fold_and_compute_round_packed<EF: ExtensionField<PF<EF>>, N>(
    nums: &[N],
    dens: &[EFPacking<EF>],
    layer_chunk_log_old: usize,
    prev_r: EF,
    eq_outer: &[EF],
    eq_within: &[EFPacking<EF>],
) -> (
    Vec<EFPacking<EF>>,
    Vec<EFPacking<EF>>,
    EFPacking<EF>,
    EFPacking<EF>,
    EFPacking<EF>,
    EFPacking<EF>,
)
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

    let (c0s, c2s, c0d, c2d) = nums
        .par_chunks_exact(in_packed)
        .zip(dens.par_chunks_exact(in_packed))
        .zip(new_nums.par_chunks_exact_mut(out_packed))
        .zip(new_dens.par_chunks_exact_mut(out_packed))
        .enumerate()
        .fold(coeffs4_zero::<EF>, |mut acc, (c, (((n_c, d_c), nn_c), nd_c))| {
            let eq_o: EF = eq_outer.get(c).copied().unwrap_or(EF::ONE);
            let mut local = coeffs4_zero::<EF>();
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

                let eq_w = eq_within[i];
                let (c0_s, c2_s) = sumcheck_quadratic(((&fl_dl, &fr_dl), (&fl_dr, &fr_dr)));
                let (c0_a, c2_a) = sumcheck_quadratic(((&fl_nl, &fr_nl), (&fl_dr, &fr_dr)));
                let (c0_b, c2_b) = sumcheck_quadratic(((&fl_nr, &fr_nr), (&fl_dl, &fr_dl)));
                local.0 += c0_s * eq_w;
                local.1 += c2_s * eq_w;
                local.2 += (c0_a + c0_b) * eq_w;
                local.3 += (c2_a + c2_b) * eq_w;
            }
            acc.0 += local.0 * eq_o;
            acc.1 += local.1 * eq_o;
            acc.2 += local.2 * eq_o;
            acc.3 += local.3 * eq_o;
            acc
        })
        .reduce(coeffs4_zero::<EF>, coeffs4_add::<EF>);

    (new_nums, new_dens, c0s, c2s, c0d, c2d)
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

fn fold_ext_active_at_bit<EF: ExtensionField<PF<EF>>>(
    m: &[EFPacking<EF>],
    alpha: EF,
    bit: usize,
    chunk_log_old: usize,
) -> Vec<EFPacking<EF>> {
    let w = packing_log_width::<EF>();
    let in_packed = 1usize << (chunk_log_old - w);
    debug_assert!(m.len().is_multiple_of(in_packed));
    let active_out = m.len() / 2;
    let stride = 1usize << bit;
    let lo_mask = stride - 1;

    let mut out: Vec<EFPacking<EF>> = unsafe { uninitialized_vec(active_out) };

    let compute = |(new_j, slot): (usize, &mut EFPacking<EF>)| {
        let i_hi = new_j >> bit;
        let i_lo = new_j & lo_mask;
        let i0 = (i_hi << (bit + 1)) | i_lo;
        let i1 = i0 | stride;
        let diff = m[i1] - m[i0];
        *slot = diff * alpha + m[i0];
    };

    if active_out < PARALLEL_THRESHOLD {
        out.iter_mut().enumerate().for_each(compute);
    } else {
        out.par_iter_mut()
            .with_min_len(PARALLEL_THRESHOLD)
            .enumerate()
            .for_each(compute);
    }

    out
}

pub(super) fn even_odd_split<EF: Copy>(v: &[EF]) -> (Vec<EF>, Vec<EF>) {
    (
        v.iter().step_by(2).copied().collect(),
        v.iter().skip(1).step_by(2).copied().collect(),
    )
}
