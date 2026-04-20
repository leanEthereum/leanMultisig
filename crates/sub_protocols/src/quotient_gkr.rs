use std::borrow::Cow;

use backend::*;
use tracing::instrument;

use crate::N_VARS_TO_SEND_GKR_COEFFS;

// Right-to-left GKR for Σ nᵢ/dᵢ.
// Storage is lexicographic (x_0 = MSB, x_{L-1} = LSB); each round binds the
// LSB. Phase 1 keeps data chunk-bit-reversed at chunk_log = min(PIVOT, L) and
// packed — a natural-LSB fold becomes a fold at the chunk-MSB, which stays
// above SIMD-lane while chunk_log > w. Once chunk_log drops to w we unpack and
// continue naturally.
//
// In this file, "br" means "bit reverse"

pub const ENDIANNESS_PIVOT_GKR: usize = 12;

enum LayerStorage<'a, EF: ExtensionField<PF<EF>>> {
    Initial {
        nums: Cow<'a, [PFPacking<EF>]>,
        dens: Cow<'a, [EFPacking<EF>]>,
        chunk_log: usize,
    },
    PackedBr {
        nums: Cow<'a, [EFPacking<EF>]>,
        dens: Cow<'a, [EFPacking<EF>]>,
        chunk_log: usize,
    },
    Natural {
        nums: Cow<'a, [EF]>,
        dens: Cow<'a, [EF]>,
    },
}

impl<'a, EF: ExtensionField<PF<EF>>> LayerStorage<'a, EF> {
    fn unpack_and_unreverse(&self) -> (Vec<EF>, Vec<EF>) {
        match self {
            LayerStorage::Initial { nums, dens, chunk_log } => {
                let n_nat: Vec<EF> = bit_reverse_chunks(PFPacking::<EF>::unpack_slice(nums.as_ref()), *chunk_log)
                    .into_iter()
                    .map(EF::from)
                    .collect();
                (n_nat, unpack_and_unreverse_slice(dens.as_ref(), *chunk_log))
            }
            LayerStorage::PackedBr { nums, dens, chunk_log } => (
                unpack_and_unreverse_slice(nums.as_ref(), *chunk_log),
                unpack_and_unreverse_slice(dens.as_ref(), *chunk_log),
            ),
            LayerStorage::Natural { nums, dens } => (nums.to_vec(), dens.to_vec()),
        }
    }
}

pub fn prove_gkr_quotient<EF: ExtensionField<PF<EF>>>(
    prover_state: &mut impl FSProver<EF>,
    numerators: &MleRef<'_, EF>,
    denominators: &MleRef<'_, EF>,
) -> (EF, MultilinearPoint<EF>, EF, EF) {
    assert_eq!(numerators.n_vars(), denominators.n_vars());
    assert!(numerators.n_vars() > N_VARS_TO_SEND_GKR_COEFFS);

    let l = numerators.n_vars();
    let w = packing_log_width::<EF>();
    let pivot = ENDIANNESS_PIVOT_GKR.min(l);
    assert!(pivot > w && l > w);

    let (MleRef::BasePacked(nums_src), MleRef::ExtensionPacked(dens_src)) = (numerators, denominators) else {
        panic!("prove_gkr_quotient requires BasePacked numerators and ExtensionPacked denominators");
    };
    let nums_nat = PFPacking::<EF>::unpack_slice(nums_src);
    let dens_nat = unpack_extension::<EF>(dens_src);
    let initial = LayerStorage::Initial {
        nums: Cow::Owned(bit_reverse_chunks_and_pack_base::<EF>(nums_nat, pivot)),
        dens: Cow::Owned(bit_reverse_chunks_and_pack::<EF>(&dens_nat, pivot)),
        chunk_log: pivot,
    };
    prove_gkr_quotient_from_initial_layer(prover_state, initial, l)
}

#[instrument(skip_all, name = "prove GKR")]
pub fn prove_gkr_quotient_br<'a, EF: ExtensionField<PF<EF>>>(
    prover_state: &mut impl FSProver<EF>,
    nums_br: &'a [PFPacking<EF>],
    dens_br: &'a [EFPacking<EF>],
    l: usize,
) -> (EF, MultilinearPoint<EF>, EF, EF) {
    let w = packing_log_width::<EF>();
    let pivot = ENDIANNESS_PIVOT_GKR.min(l);
    assert!(l > N_VARS_TO_SEND_GKR_COEFFS);
    assert!(
        pivot > w && l > w,
        "prove_gkr_quotient_from_packed_br_base requires packed mode"
    );
    assert_eq!(nums_br.len() << w, 1 << l);
    assert_eq!(dens_br.len() << w, 1 << l);
    let initial = LayerStorage::Initial {
        nums: Cow::Borrowed(nums_br),
        dens: Cow::Borrowed(dens_br),
        chunk_log: pivot,
    };
    prove_gkr_quotient_from_initial_layer(prover_state, initial, l)
}

fn prove_gkr_quotient_from_initial_layer<'a, EF: ExtensionField<PF<EF>>>(
    prover_state: &mut impl FSProver<EF>,
    initial: LayerStorage<'a, EF>,
    l: usize,
) -> (EF, MultilinearPoint<EF>, EF, EF) {
    let w = packing_log_width::<EF>();
    let mut layers: Vec<LayerStorage<'a, EF>> = vec![initial];

    // Phase 1: SIMD reductions on packed-BR data until chunk_log shrinks to w.
    let mut current_n_vars = l;
    while current_n_vars > N_VARS_TO_SEND_GKR_COEFFS {
        let (new_nums, new_dens, new_chunk_log) = match layers.last().unwrap() {
            LayerStorage::Initial { nums, dens, chunk_log } if *chunk_log > w => {
                let (nn, nd) = sum_quotients_packed_br::<EF, _>(nums.as_ref(), dens.as_ref(), *chunk_log);
                (nn, nd, *chunk_log - 1)
            }
            LayerStorage::PackedBr { nums, dens, chunk_log } if *chunk_log > w => {
                let (nn, nd) = sum_quotients_packed_br::<EF, _>(nums.as_ref(), dens.as_ref(), *chunk_log);
                (nn, nd, *chunk_log - 1)
            }
            _ => break,
        };
        layers.push(LayerStorage::PackedBr {
            nums: Cow::Owned(new_nums),
            dens: Cow::Owned(new_dens),
            chunk_log: new_chunk_log,
        });
        current_n_vars -= 1;
    }

    while current_n_vars > N_VARS_TO_SEND_GKR_COEFFS {
        let (n_nat, d_nat) = layers.last().unwrap().unpack_and_unreverse();
        let (nn, nd) = sum_quotients(&n_nat, &d_nat);
        layers.push(LayerStorage::Natural {
            nums: Cow::Owned(nn),
            dens: Cow::Owned(nd),
        });
        current_n_vars -= 1;
    }

    let top = layers.pop().unwrap();
    let (top_nums, top_dens) = top.unpack_and_unreverse();
    prover_state.add_extension_scalars(&top_nums);
    prover_state.add_extension_scalars(&top_dens);
    let quotient = compute_quotient(&top_nums, &top_dens);

    let mut point = MultilinearPoint(prover_state.sample_vec(N_VARS_TO_SEND_GKR_COEFFS));
    let mut claim_num = top_nums.evaluate(&point);
    let mut claim_den = top_dens.evaluate(&point);

    for layer in layers.iter().rev() {
        let (next_point, next_num, next_den) =
            prove_gkr_quotient_step(prover_state, layer, &point, claim_num, claim_den);
        point = next_point;
        claim_num = next_num;
        claim_den = next_den;
    }

    (quotient, point, claim_num, claim_den)
}

fn prove_gkr_quotient_step<EF: ExtensionField<PF<EF>>>(
    prover_state: &mut impl FSProver<EF>,
    layer: &LayerStorage<'_, EF>,
    claim_point: &MultilinearPoint<EF>, // K coords, natural order
    claim_num: EF,
    claim_den: EF,
) -> (MultilinearPoint<EF>, EF, EF) {
    let alpha = prover_state.sample();
    let expected_sum = claim_num + alpha * claim_den;
    let w = packing_log_width::<EF>();

    // Run SIMD rounds when L/R chunks are wider than one packed word
    // (chunk_log > w+1); otherwise fall back to the unpacked sumcheck.
    let (mut q_natural, inner_evals) = match layer {
        LayerStorage::Initial { nums, dens, chunk_log } if *chunk_log > w + 1 => {
            rtl_gkr_quotient_sumcheck_prove_packed_br_base(
                prover_state,
                nums.as_ref(),
                dens.as_ref(),
                *chunk_log,
                &claim_point.0,
                alpha,
                expected_sum,
            )
        }
        LayerStorage::PackedBr { nums, dens, chunk_log } if *chunk_log > w + 1 => {
            rtl_gkr_quotient_sumcheck_prove_packed_br(
                prover_state,
                nums.as_ref(),
                dens.as_ref(),
                *chunk_log,
                &claim_point.0,
                alpha,
                expected_sum,
            )
        }
        _ => {
            let (n_nat, d_nat) = layer.unpack_and_unreverse();
            let (num_l, num_r) = even_odd_split(&n_nat);
            let (den_l, den_r) = even_odd_split(&d_nat);
            rtl_gkr_quotient_sumcheck_prove(
                prover_state,
                num_l,
                num_r,
                den_l,
                den_r,
                &claim_point.0,
                alpha,
                expected_sum,
            )
        }
    };

    prover_state.add_extension_scalars(&inner_evals);
    let beta = prover_state.sample();
    let [nl_q, nr_q, dl_q, dr_q] = inner_evals;
    let one_minus_beta = EF::ONE - beta;
    let next_num = one_minus_beta * nl_q + beta * nr_q;
    let next_den = one_minus_beta * dl_q + beta * dr_q;

    q_natural.push(beta);
    (MultilinearPoint(q_natural), next_num, next_den)
}

// Runs the RTL sumcheck proving
//   Σ_b eq(b, eq_point) · [nl(b)·dr(b) + nr(b)·dl(b) + α·dl(b)·dr(b)] = expected_sum,
// binding the LSB first. Returns (q_natural, [nl(q), nr(q), dl(q), dr(q)]).
#[allow(clippy::too_many_arguments)]
fn rtl_gkr_quotient_sumcheck_prove<EF: ExtensionField<PF<EF>>>(
    prover_state: &mut impl FSProver<EF>,
    num_l: Vec<EF>,
    num_r: Vec<EF>,
    den_l: Vec<EF>,
    den_r: Vec<EF>,
    eq_point: &[EF],
    alpha: EF,
    expected_sum: EF,
) -> (Vec<EF>, [EF; 4]) {
    rtl_gkr_quotient_sumcheck_prove_unpacked_rounds(
        prover_state,
        num_l,
        num_r,
        den_l,
        den_r,
        eq_point.to_vec(),
        Vec::with_capacity(eq_point.len()),
        alpha,
        expected_sum,
        EF::ONE,
    )
}

// Invariant entering round r: sum = mmf · H_r(r_0,…,r_{r-1}),
// mmf = Π_{i<r} eq(α_i, r_i). The bare polynomial sent is mmf · H_r(z).
// α is applied once per round at finalize (saves 2 mults per pair).
#[allow(clippy::too_many_arguments)]
fn rtl_gkr_quotient_sumcheck_prove_unpacked_rounds<EF: ExtensionField<PF<EF>>>(
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

// Phase-1 SIMD sumcheck on packed-BR data. Folds the chunk-MSB packed bit
// each round; transitions to the unpacked loop once the next fold would cross
// lane boundaries. SplitEq keeps the eq table factorized (O(√N) build per
// round); fold+compute are fused from round 1 onward.
#[allow(clippy::too_many_arguments)]
fn rtl_gkr_quotient_sumcheck_prove_packed_br<EF: ExtensionField<PF<EF>>>(
    prover_state: &mut impl FSProver<EF>,
    packed_nums: &[EFPacking<EF>],
    packed_dens: &[EFPacking<EF>],
    parent_chunk_log: usize,
    eq_point: &[EF],
    alpha: EF,
    expected_sum: EF,
) -> (Vec<EF>, [EF; 4]) {
    let w = packing_log_width::<EF>();
    debug_assert!(parent_chunk_log > w + 1);
    debug_assert_eq!(packed_nums.len(), packed_dens.len());
    run_phase1_packed(
        prover_state,
        Cow::Borrowed(packed_nums),
        Cow::Borrowed(packed_dens),
        parent_chunk_log,
        eq_point.to_vec(),
        Vec::with_capacity(eq_point.len()),
        alpha,
        expected_sum,
        EF::ONE,
        None,
        None,
    )
}

/// Base-numerator variant: runs round 0 as base×ext for full base-field
/// density, then folds into EFPacking and continues via `run_phase1_packed`.
#[allow(clippy::too_many_arguments)]
fn rtl_gkr_quotient_sumcheck_prove_packed_br_base<EF: ExtensionField<PF<EF>>>(
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
    let mut q_natural: Vec<EF> = Vec::with_capacity(k);
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

    // Round 1 fused (base→ext fold + compute): needs 3 packed bits (sib, r0, r1).
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

        run_phase1_packed(
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
        run_phase1_packed(
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

#[inline(always)]
fn within_pt<EF: Copy>(remaining_eq: &[EF], head_len: usize) -> Vec<EF> {
    remaining_eq[head_len..remaining_eq.len() - 1]
        .iter()
        .rev()
        .copied()
        .collect()
}

/// Combine the (c0,c2) packed pairs, sample the next challenge, and advance
/// `sum`/`mmf` accordingly.
#[allow(clippy::too_many_arguments)]
#[inline(always)]
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

/// Phase-1 SIMD sumcheck on packed-BR combined-view data. The L/R sibling bit
/// is the chunk-MSB. Round 0 uses unfused compute; subsequent rounds fuse the
/// prev-round fold with the current compute in a single sweep. Transitions to
/// the unpacked loop once chunks shrink to one packed word.
#[allow(clippy::too_many_arguments)]
fn run_phase1_packed<'a, EF: ExtensionField<PF<EF>>>(
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

    // Drain any pending fold before transitioning to the unpacked loop.
    if let Some(prev_r) = pending_r {
        let prev_bit = layer_chunk_log - 1 - w;
        nums = Cow::Owned(fold_multilinear_at_bit(nums.as_ref(), prev_r, prev_bit, &|v, a| v * a));
        dens = Cow::Owned(fold_multilinear_at_bit(dens.as_ref(), prev_r, prev_bit, &|v, a| v * a));
    }

    let nums_nat = unpack_and_unreverse_slice(nums.as_ref(), layer_chunk_log);
    let dens_nat = unpack_and_unreverse_slice(dens.as_ref(), layer_chunk_log);
    let (num_l, num_r) = even_odd_split(&nums_nat);
    let (den_l, den_r) = even_odd_split(&dens_nat);
    rtl_gkr_quotient_sumcheck_prove_unpacked_rounds(
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

/// Combined-view compute for one phase-1 round. `nums` may be `EFPacking` or
/// `PFPacking`; the generic bound `EFPacking<EF>: Algebra<N>` handles both.
/// Iterates outer-chunk first so `eq_outer[c]` costs one scalar mult per chunk.
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

/// Combined-view fused fold + compute for phase-1: folds the prev bit into
/// new arrays at `chunk_log - 1` AND computes the next round polynomial.
/// Generic over the numerator element type `N`: `EFPacking<EF>` for the
/// general case, `PFPacking<EF>` for the base→ext lift on the top layer.
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
                // (sib, prev, cur) strides = (in_half, in_quarter, in_eighth).
                let l_p0_c0 = i;
                let l_p0_c1 = i + in_eighth;
                let l_p1_c0 = i + in_quarter;
                let l_p1_c1 = i + in_quarter + in_eighth;
                let r_p0_c0 = i + in_half;
                let r_p0_c1 = i + in_half + in_eighth;
                let r_p1_c0 = i + in_half + in_quarter;
                let r_p1_c1 = i + in_half + in_quarter + in_eighth;

                // prev_r_packed * diff works for both N = EFPacking (trivially)
                // and N = PFPacking (via Algebra<PFPacking>), uniformly lifting
                // the nums fold into EFPacking.
                let fl_nl: EFPacking<EF> = prev_r_packed * (n_c[l_p1_c0] - n_c[l_p0_c0]) + n_c[l_p0_c0];
                let fr_nl: EFPacking<EF> = prev_r_packed * (n_c[l_p1_c1] - n_c[l_p0_c1]) + n_c[l_p0_c1];
                let fl_nr: EFPacking<EF> = prev_r_packed * (n_c[r_p1_c0] - n_c[r_p0_c0]) + n_c[r_p0_c0];
                let fr_nr: EFPacking<EF> = prev_r_packed * (n_c[r_p1_c1] - n_c[r_p0_c1]) + n_c[r_p0_c1];
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

/// Build the bare round polynomial (scaled by `mmf`) from the z⁰ and z²
/// coefficients of `H(z)`; h(1) is recovered from the sum constraint.
#[inline(always)]
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

pub fn verify_gkr_quotient<EF: ExtensionField<PF<EF>>>(
    verifier_state: &mut impl FSVerifier<EF>,
    n_vars: usize,
) -> Result<(EF, MultilinearPoint<EF>, EF, EF), ProofError> {
    assert!(n_vars > N_VARS_TO_SEND_GKR_COEFFS);
    let send_len = 1 << N_VARS_TO_SEND_GKR_COEFFS;
    let last_nums = verifier_state.next_extension_scalars_vec(send_len)?;
    let last_dens = verifier_state.next_extension_scalars_vec(send_len)?;
    let quotient: EF = compute_quotient(&last_nums, &last_dens);
    let mut point = MultilinearPoint(verifier_state.sample_vec(N_VARS_TO_SEND_GKR_COEFFS));
    let mut claims_num = last_nums.evaluate(&point);
    let mut claims_den = last_dens.evaluate(&point);
    for i in N_VARS_TO_SEND_GKR_COEFFS..n_vars {
        (point, claims_num, claims_den) = verify_gkr_quotient_step(verifier_state, i, &point, claims_num, claims_den)?;
    }
    Ok((quotient, point, claims_num, claims_den))
}

fn verify_gkr_quotient_step<EF: ExtensionField<PF<EF>>>(
    verifier_state: &mut impl FSVerifier<EF>,
    n_vars: usize,
    point: &MultilinearPoint<EF>,
    claims_num: EF,
    claims_den: EF,
) -> Result<(MultilinearPoint<EF>, EF, EF), ProofError> {
    let alpha = verifier_state.sample();
    let expected_sum = claims_num + alpha * claims_den;
    let eq_alphas_rev: Vec<EF> = point.0.iter().rev().copied().collect();
    let mut postponed = sumcheck_verify(verifier_state, n_vars, 3, expected_sum, Some(&eq_alphas_rev))?;
    postponed.point.0.reverse();
    let inner_evals = verifier_state.next_extension_scalars_vec(4)?;
    let constraints_eval =
        alpha * inner_evals[2] * inner_evals[3] + (inner_evals[0] * inner_evals[3] + inner_evals[1] * inner_evals[2]);
    if postponed.value != point.eq_poly_outside(&postponed.point) * constraints_eval {
        return Err(ProofError::InvalidProof);
    }
    let beta = verifier_state.sample();
    let next_claims_numerators = (&inner_evals[..2]).evaluate(&MultilinearPoint(vec![beta]));
    let next_claims_denominators = (&inner_evals[2..]).evaluate(&MultilinearPoint(vec![beta]));
    let mut next_point = postponed.point.clone();
    next_point.0.push(beta);
    Ok((next_point, next_claims_numerators, next_claims_denominators))
}

fn sum_quotients<EF: ExtensionField<PF<EF>>>(nums: &[EF], dens: &[EF]) -> (Vec<EF>, Vec<EF>) {
    let n = nums.len();
    assert_eq!(n, dens.len());
    let new_n = n / 2;
    let mut new_nums = unsafe { uninitialized_vec(new_n) };
    let mut new_dens = unsafe { uninitialized_vec(new_n) };
    new_nums
        .par_iter_mut()
        .zip(new_dens.par_iter_mut())
        .enumerate()
        .for_each(|(i, (num, den))| {
            // LSB pairing: combine storage positions 2i and 2i+1.
            let n0 = nums[2 * i];
            let n1 = nums[2 * i + 1];
            let d0 = dens[2 * i];
            let d1 = dens[2 * i + 1];
            *num = d1 * n0 + d0 * n1;
            *den = d0 * d1;
        });
    (new_nums, new_dens)
}

fn compute_quotient<EF: ExtensionField<PF<EF>>>(numerators: &[EF], denominators: &[EF]) -> EF {
    numerators.iter().zip(denominators).map(|(&n, &d)| n / d).sum()
}

fn even_odd_split<EF: Copy>(v: &[EF]) -> (Vec<EF>, Vec<EF>) {
    (
        v.iter().step_by(2).copied().collect(),
        v.iter().skip(1).step_by(2).copied().collect(),
    )
}

/// Bit-reverse each `2^chunk_log`-sized chunk of `v` (unpacked, any element
/// type). Bit-reversal is an involution, so this is also its own inverse.
fn bit_reverse_chunks<T: Copy + Send + Sync>(v: &[T], chunk_log: usize) -> Vec<T> {
    let n = v.len();
    debug_assert!(n.is_power_of_two());
    debug_assert!(chunk_log <= n.trailing_zeros() as usize);
    let mut out: Vec<T> = unsafe { uninitialized_vec(n) };
    bit_reverse_chunks_into(v, chunk_log, &mut out);
    out
}

fn bit_reverse_chunks_into<T: Copy + Send + Sync>(v: &[T], chunk_log: usize, out: &mut [T]) {
    let n = v.len();
    assert_eq!(n, out.len());
    debug_assert!(n.is_power_of_two());
    debug_assert!(chunk_log <= n.trailing_zeros() as usize);
    if chunk_log == 0 {
        out.copy_from_slice(v);
        return;
    }
    let chunk_size = 1usize << chunk_log;
    let shift = usize::BITS as usize - chunk_log;
    out.par_chunks_exact_mut(chunk_size)
        .zip(v.par_chunks_exact(chunk_size))
        .for_each(|(dst, src)| {
            for (p, slot) in dst.iter_mut().enumerate() {
                *slot = src[p.reverse_bits() >> shift];
            }
        });
}

/// Natural-order extension-field slice → chunk-bit-reversed + packed.
pub fn bit_reverse_chunks_and_pack<EF: ExtensionField<PF<EF>>>(v: &[EF], chunk_log: usize) -> Vec<EFPacking<EF>> {
    pack_extension(&bit_reverse_chunks(v, chunk_log))
}

/// Base-field analogue: natural-order `&[PF]` → chunk-bit-reversed + packed.
pub fn bit_reverse_chunks_and_pack_base<EF: ExtensionField<PF<EF>>>(
    v: &[PF<EF>],
    chunk_log: usize,
) -> Vec<PFPacking<EF>> {
    let width: usize = packing_width::<EF>();
    let mut res = unsafe { uninitialized_vec::<PFPacking<EF>>(v.len() / width) };
    let unpacked = PFPacking::<EF>::unpack_slice_mut(&mut res);
    bit_reverse_chunks_into(v, chunk_log, unpacked);
    res
}

/// Inverse of `bit_reverse_chunks_and_pack` for ext-packed slices.
fn unpack_and_unreverse_slice<EF: ExtensionField<PF<EF>>>(v: &[EFPacking<EF>], chunk_log: usize) -> Vec<EF> {
    bit_reverse_chunks(&unpack_extension::<EF>(v), chunk_log)
}

fn sum_quotients_packed_br<EF: ExtensionField<PF<EF>>, N>(
    nums: &[N],
    dens: &[EFPacking<EF>],
    chunk_log: usize,
) -> (Vec<EFPacking<EF>>, Vec<EFPacking<EF>>)
where
    N: Copy + Send + Sync,
    EFPacking<EF>: Algebra<N>,
{
    let w = packing_log_width::<EF>();
    debug_assert!(chunk_log > w);
    debug_assert_eq!(nums.len(), dens.len());

    let bit = chunk_log - 1 - w;
    let stride = 1usize << bit;
    let lo_mask = stride - 1;
    let new_packed_len = nums.len() / 2;

    let mut new_nums: Vec<EFPacking<EF>> = unsafe { uninitialized_vec(new_packed_len) };
    let mut new_dens: Vec<EFPacking<EF>> = unsafe { uninitialized_vec(new_packed_len) };

    new_nums
        .par_iter_mut()
        .zip(new_dens.par_iter_mut())
        .enumerate()
        .for_each(|(new_j, (num_out, den_out))| {
            let i_hi = new_j >> bit;
            let i_lo = new_j & lo_mask;
            let i0 = (i_hi << (bit + 1)) | i_lo;
            let i1 = i0 | stride;
            *num_out = dens[i1] * nums[i0] + dens[i0] * nums[i1];
            *den_out = dens[i0] * dens[i1];
        });

    (new_nums, new_dens)
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use super::*;
    use rand::{RngExt, SeedableRng, rngs::StdRng};
    use utils::{build_prover_state, build_verifier_state, init_tracing};

    type F = KoalaBear;
    type EF = QuinticExtensionFieldKB;

    fn sum_all_quotients(nums: &[F], den: &[EF]) -> EF {
        nums.par_iter().zip(den).map(|(&n, &d)| EF::from(n) / d).sum()
    }

    fn run_gkr_quotient(log_n: usize) {
        let n = 1 << log_n;

        let mut rng = StdRng::seed_from_u64(0);
        let numerators = (0..n).map(|_| rng.random()).collect::<Vec<F>>();
        let c: EF = rng.random();
        let denominators_indexes = (0..n)
            .map(|_| PF::<EF>::from_usize(rng.random_range(..n)))
            .collect::<Vec<_>>();
        let denominators = denominators_indexes.iter().map(|&i| c - i).collect::<Vec<EF>>();
        let real_quotient = sum_all_quotients(&numerators, &denominators);
        let mut prover_state = build_prover_state();

        let numerators = MleOwned::BasePacked(pack_extension(&numerators));
        let denominators = MleOwned::ExtensionPacked(pack_extension(&denominators));

        let time = Instant::now();
        let prover_statements =
            prove_gkr_quotient::<EF>(&mut prover_state, &numerators.by_ref(), &denominators.by_ref());
        println!("Proving time: {:.3}", time.elapsed().as_secs_f64());

        let mut verifier_state = build_verifier_state(prover_state).unwrap();
        let verifier_statements = verify_gkr_quotient::<EF>(&mut verifier_state, log_n).unwrap();
        assert_eq!(&verifier_statements, &prover_statements);
        let (retrieved_quotient, claim_point, claim_num, claim_den) = verifier_statements;
        assert_eq!(retrieved_quotient, real_quotient);
        assert_eq!(numerators.evaluate(&claim_point), claim_num);
        assert_eq!(denominators.evaluate(&claim_point), claim_den);
    }

    #[test]
    #[ignore]
    fn bench_gkr_quotient() {
        init_tracing();
        let log_n = 25;
        run_gkr_quotient(log_n);
    }

    #[test]
    fn test_gkr_quotient() {
        init_tracing();
        for log_n in [8, 11, 15] {
            run_gkr_quotient(log_n);
        }
    }
}
