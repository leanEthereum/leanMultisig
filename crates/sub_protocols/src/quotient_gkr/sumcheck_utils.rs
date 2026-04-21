use std::borrow::Cow;

use backend::*;

use crate::quotient_gkr::unpack_and_unreverse_slice;

#[inline(always)]
fn within_pt<EF: Copy>(remaining_eq: &[EF], head_len: usize) -> Vec<EF> {
    remaining_eq[head_len..remaining_eq.len() - 1]
        .iter()
        .rev()
        .copied()
        .collect()
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
) -> EF {
    let c0_raw: EF = EFPacking::<EF>::to_ext_iter([c0_d + c0_s * alpha]).sum();
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

    let k = eq_point.len();
    let mut remaining_eq = eq_point.to_vec();
    // head_len = outer bits above parent_chunk_log (the combined view includes
    // the sibling bit inside the chunk).
    let head_len = (k + 1).saturating_sub(parent_chunk_log);
    let mut q_natural = vec![];
    let mut mmf = EF::ONE;
    let mut sum = expected_sum;

    let eq_outer: Vec<EF> = if head_len == 0 {
        vec![EF::ONE]
    } else {
        eval_eq(&remaining_eq[..head_len])
    };

    // Round 0: base × ext directly on the combined layer.
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
    );
    q_natural.insert(0, r0);
    remaining_eq.pop();

    if parent_chunk_log >= w + 3 && remaining_eq.len() > w + 1 {
        let eq_alpha_1 = *remaining_eq.last().unwrap();
        let eq_within_1 = eval_eq_packed(&within_pt(&remaining_eq, head_len));
        let (nums_ext, dens_ext, c0_s, c2_s, c0_d, c2_d) = fold_and_compute_round_packed::<EF, _>(
            packed_nums,
            packed_dens,
            parent_chunk_log,
            r0,
            &eq_outer,
            &eq_within_1,
        );
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
    } else {
        // Tiny-layer fallback: unfused fold.
        let fold_bit = parent_chunk_log - 2 - w;
        let nums_ext = fold_base_to_ext_at_bit::<EF>(packed_nums, r0, fold_bit);
        let dens_ext = fold_multilinear_at_bit(packed_dens, r0, fold_bit, &|v, a| v * a);
        run_phase1_sumcheck(
            prover_state,
            Cow::Owned(nums_ext),
            Cow::Owned(dens_ext),
            parent_chunk_log - 1,
            remaining_eq,
            q_natural,
            alpha,
            sum,
            mmf,
            Some(eq_outer),
            None,
        )
    }
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
    let eq_outer: Vec<EF> = precomputed_eq_outer.unwrap_or_else(|| {
        if head_len == 0 {
            vec![EF::ONE]
        } else {
            eval_eq(&remaining_eq[..head_len])
        }
    });

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
        );
        pending_r = Some(r);
        layer_chunk_log -= 1;
        q_natural.insert(0, r);
        remaining_eq.pop();
    }

    if let Some(prev_r) = pending_r {
        let prev_bit = layer_chunk_log - 1 - w;
        nums = Cow::Owned(fold_multilinear_at_bit(nums.as_ref(), prev_r, prev_bit, &|v, a| v * a));
        dens = Cow::Owned(fold_multilinear_at_bit(dens.as_ref(), prev_r, prev_bit, &|v, a| v * a));
    }

    let nums_nat = unpack_and_unreverse_slice(nums.as_ref(), layer_chunk_log);
    let dens_nat = unpack_and_unreverse_slice(dens.as_ref(), layer_chunk_log);
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


// Normal ordering (not bit-reversed) + not packed
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
        let eq_table = if eq_prefix.is_empty() {
            vec![EF::ONE]
        } else {
            eval_eq(eq_prefix)
        };

        let half = num_l.len() / 2;
        debug_assert_eq!(eq_table.len(), half);

        let mut c0_s_raw = EF::ZERO;
        let mut c2_s_raw = EF::ZERO;
        let mut c0_d_raw = EF::ZERO;
        let mut c2_d_raw = EF::ZERO;
        for j in 0..half {
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

        let bare = build_bare_from_coeffs(
            c0_d_raw + alpha * c0_s_raw,
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

        let fold = |v: &[EF]| fold_multilinear_lsb(v, r, &|diff, a| a * diff);
        num_l = fold(&num_l);
        num_r = fold(&num_r);
        den_l = fold(&den_l);
        den_r = fold(&den_r);

        q_natural.insert(0, r);
        remaining_eq.pop();
    }

    debug_assert_eq!(num_l.len(), 1);
    let evals = [num_l[0], num_r[0], den_l[0], den_r[0]];
    (q_natural, evals)
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

    let new_len = nums.len() / 2;
    let mut new_nums: Vec<EFPacking<EF>> = unsafe { uninitialized_vec(new_len) };
    let mut new_dens: Vec<EFPacking<EF>> = unsafe { uninitialized_vec(new_len) };
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

/// Fold a base-field-packed array at `bit`, producing an extension-field
/// packed result.
fn fold_base_to_ext_at_bit<EF: ExtensionField<PF<EF>>>(m: &[PFPacking<EF>], alpha: EF, bit: usize) -> Vec<EFPacking<EF>>
where
    EFPacking<EF>: Algebra<PFPacking<EF>>,
{
    let alpha_packed: EFPacking<EF> = <EFPacking<EF> as From<EF>>::from(alpha);
    fold_multilinear_at_bit(m, alpha_packed, bit, &|diff, a| a * diff)
}



pub(super) fn even_odd_split<EF: Copy>(v: &[EF]) -> (Vec<EF>, Vec<EF>) {
    (
        v.iter().step_by(2).copied().collect(),
        v.iter().skip(1).step_by(2).copied().collect(),
    )
}