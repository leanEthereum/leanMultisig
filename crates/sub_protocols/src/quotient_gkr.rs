use std::borrow::Cow;

use backend::*;
use tracing::{info_span, instrument};

use crate::N_VARS_TO_SEND_GKR_COEFFS;

/*
GKR to compute a sum of fractions, right-to-left variant.

Conventions (same as crates/sub_protocols/src/air_sumcheck.rs):
  - MLE storage is lexicographic: for a MultilinearPoint (x_0, ..., x_{L-1}),
    x_0 is the MSB of the storage index and x_{L-1} is the LSB.
  - Variables are bound right-to-left: round 0 binds X_{K-1} (the LSB of the
    storage), round r binds X_{K-1-r}. Accordingly the GKR layer reduction
    collapses the LSB (pairs (2i, 2i+1)), and the per-layer sumcheck also
    folds the LSB first.

SIMD layout for the GKR reductions (phase-1 only, for now):
  - On entry we chunk-bit-reverse each column within chunks of size 2^P
    (P = min(ENDIANNESS_PIVOT, L)), and promote to EFPacking<EF>.
  - A natural-LSB fold then becomes a fold at the *chunk-MSB* storage bit,
    i.e. paired storage indices differ only at bit (chunk_log - 1). In
    packed space that is packed-index bit (chunk_log - 1 - w). As long as
    chunk_log > w, the pair lives in different packed words → fully SIMD.
  - Each reduction shrinks chunk_log by 1. Once chunk_log drops to w (one
    packed word per chunk), further folds would have to be within-lane; we
    fall back to unpacked natural-order Vec<EF> for the remaining reductions
    and for the per-layer sumchecks (sumcheck SIMD is a follow-up).
*/

pub const ENDIANNESS_PIVOT: usize = 12;

/// A GKR layer, stored either in packed bit-reversed form (phase-1, keeps SIMD
/// available to the per-layer sumcheck) or in natural-order unpacked form
/// (phase-2 and beyond, once chunks have shrunk to a single packed word).
///
/// `PackedBrBase` applies only to the BIGGEST layer (before any reduction):
/// the original numerators are base-field, so we keep them as `PFPacking` to
/// preserve base-field SIMD density in the first reduction + the first round
/// of the biggest sumcheck.  After one reduction, num × den products live in
/// the extension field, so subsequent layers use `PackedBr`.
enum LayerStorage<EF: ExtensionField<PF<EF>>> {
    PackedBrBase {
        nums: Vec<PFPacking<EF>>,
        dens: Vec<EFPacking<EF>>,
        chunk_log: usize,
    },
    PackedBr {
        nums: Vec<EFPacking<EF>>,
        dens: Vec<EFPacking<EF>>,
        chunk_log: usize,
    },
    Natural {
        nums: Vec<EF>,
        dens: Vec<EF>,
    },
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
    let pivot = ENDIANNESS_PIVOT.min(l);

    let use_packed = pivot > w && l > w;

    // Biggest layer, stored as packed-BR when SIMD is available.  Otherwise we
    // fall back to natural-order unpacked.
    let initial = if use_packed {
        // Keep base-field numerators in PFPacking when the input provides
        // them — the biggest reduction and the biggest sumcheck's round 0 get
        // the full base-field density.
        match (numerators, denominators) {
            (MleRef::BasePacked(nums_src), MleRef::ExtensionPacked(dens_src)) => {
                let nums_nat = PFPacking::<EF>::unpack_slice(nums_src);
                let dens_nat = unpack_extension_fast::<EF>(dens_src);
                LayerStorage::PackedBrBase {
                    nums: bit_reverse_chunks_and_pack_base::<EF>(nums_nat, pivot),
                    dens: bit_reverse_chunks_and_pack::<EF>(&dens_nat, pivot),
                    chunk_log: pivot,
                }
            }
            _ => {
                let nums_nat: Vec<EF> = mle_ref_to_vec_ef(numerators);
                let dens_nat: Vec<EF> = mle_ref_to_vec_ef(denominators);
                LayerStorage::PackedBr {
                    nums: bit_reverse_chunks_and_pack::<EF>(&nums_nat, pivot),
                    dens: bit_reverse_chunks_and_pack::<EF>(&dens_nat, pivot),
                    chunk_log: pivot,
                }
            }
        }
    } else {
        LayerStorage::Natural {
            nums: mle_ref_to_vec_ef(numerators),
            dens: mle_ref_to_vec_ef(denominators),
        }
    };
    prove_gkr_quotient_from_initial_layer(prover_state, initial, l)
}

/// Variant that takes already chunk-bit-reversed packed inputs.  The caller
/// is expected to have filled the buffers in chunk-BR order at `chunk_log =
/// min(ENDIANNESS_PIVOT, l)`.  Saves an explicit bit-reverse pass (~17 ms on
/// the xmss hot path) when fills already have chunk alignment.
#[instrument(skip_all, name = "prove GKR")]
pub fn prove_gkr_quotient_from_packed_br_base<EF: ExtensionField<PF<EF>>>(
    prover_state: &mut impl FSProver<EF>,
    nums_br: Vec<PFPacking<EF>>,
    dens_br: Vec<EFPacking<EF>>,
    l: usize,
) -> (EF, MultilinearPoint<EF>, EF, EF) {
    let w = packing_log_width::<EF>();
    let pivot = ENDIANNESS_PIVOT.min(l);
    assert!(l > N_VARS_TO_SEND_GKR_COEFFS);
    assert!(
        pivot > w && l > w,
        "prove_gkr_quotient_from_packed_br_base requires packed mode"
    );
    assert_eq!(nums_br.len() << w, 1 << l);
    assert_eq!(dens_br.len() << w, 1 << l);
    let initial = LayerStorage::PackedBrBase {
        nums: nums_br,
        dens: dens_br,
        chunk_log: pivot,
    };
    prove_gkr_quotient_from_initial_layer(prover_state, initial, l)
}

fn prove_gkr_quotient_from_initial_layer<EF: ExtensionField<PF<EF>>>(
    prover_state: &mut impl FSProver<EF>,
    initial: LayerStorage<EF>,
    l: usize,
) -> (EF, MultilinearPoint<EF>, EF, EF) {
    let w = packing_log_width::<EF>();
    let mut layers: Vec<LayerStorage<EF>> = Vec::new();
    layers.push(initial);

    // Phase-1 reductions: work on packed bit-reversed data. Each reduction
    // halves chunk_log; we stop when a chunk is down to one packed word
    // (chunk_log == w), at which point further reductions go within-lane and
    // we switch to unpacked.
    let _span = info_span!("GKR Phase 1: Packed reductions").entered();
    let mut current_n_vars = l;
    while current_n_vars > N_VARS_TO_SEND_GKR_COEFFS {
        let (new_nums, new_dens, new_chunk_log) = match layers.last().unwrap() {
            LayerStorage::PackedBrBase { nums, dens, chunk_log } if *chunk_log > w => {
                let (nn, nd) = sum_quotients_packed_br_base::<EF>(nums, dens, *chunk_log);
                (nn, nd, *chunk_log - 1)
            }
            LayerStorage::PackedBr { nums, dens, chunk_log } if *chunk_log > w => {
                let (nn, nd) = sum_quotients_packed_br::<EF>(nums, dens, *chunk_log);
                (nn, nd, *chunk_log - 1)
            }
            _ => break,
        };
        layers.push(LayerStorage::PackedBr {
            nums: new_nums,
            dens: new_dens,
            chunk_log: new_chunk_log,
        });
        current_n_vars -= 1;
    }

    // Phase-2+ reductions: unpacked natural-order. If the current last layer
    // is still in packed form, unpack+un-bit-reverse it on the fly for the
    // first reduction; subsequent iterations consume the Natural layer we push.
    while current_n_vars > N_VARS_TO_SEND_GKR_COEFFS {
        let (nn, nd) = match layers.last().unwrap() {
            LayerStorage::PackedBrBase { nums, dens, chunk_log } => {
                let n_nat: Vec<EF> = unpack_base_and_unreverse::<EF>(nums, *chunk_log)
                    .into_iter()
                    .map(EF::from)
                    .collect();
                let d_nat = unpack_and_unreverse::<EF>(dens, *chunk_log);
                sum_quotients(&n_nat, &d_nat)
            }
            LayerStorage::PackedBr { nums, dens, chunk_log } => {
                let n_nat = unpack_and_unreverse::<EF>(nums, *chunk_log);
                let d_nat = unpack_and_unreverse::<EF>(dens, *chunk_log);
                sum_quotients(&n_nat, &d_nat)
            }
            LayerStorage::Natural { nums, dens } => sum_quotients(nums, dens),
        };
        layers.push(LayerStorage::Natural { nums: nn, dens: nd });
        current_n_vars -= 1;
    }
    std::mem::drop(_span);

    // Top of GKR: must be natural for evaluation at a sampled point.
    let top = layers.pop().unwrap();
    let (top_nums, top_dens) = match top {
        LayerStorage::PackedBrBase { nums, dens, chunk_log } => (
            unpack_base_and_unreverse::<EF>(&nums, chunk_log)
                .into_iter()
                .map(EF::from)
                .collect(),
            unpack_and_unreverse::<EF>(&dens, chunk_log),
        ),
        LayerStorage::PackedBr { nums, dens, chunk_log } => (
            unpack_and_unreverse::<EF>(&nums, chunk_log),
            unpack_and_unreverse::<EF>(&dens, chunk_log),
        ),
        LayerStorage::Natural { nums, dens } => (nums, dens),
    };
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

#[instrument(skip_all)]
fn prove_gkr_quotient_step<EF: ExtensionField<PF<EF>>>(
    prover_state: &mut impl FSProver<EF>,
    layer: &LayerStorage<EF>,
    claim_point: &MultilinearPoint<EF>, // K coords, natural order
    claim_num: EF,
    claim_den: EF,
) -> (MultilinearPoint<EF>, EF, EF) {
    let alpha = prover_state.sample();
    let expected_sum = claim_num + alpha * claim_den;
    let w = packing_log_width::<EF>();

    // Dispatch on storage. We can run phase-1 SIMD rounds when the packed-BR
    // parent splits into L/R chunks of size > 2^w (i.e. parent chunk_log > w+1);
    // otherwise we unpack eagerly and run the original unpacked sumcheck.
    let (mut q_natural, inner_evals) = match layer {
        LayerStorage::PackedBrBase { nums, dens, chunk_log } if *chunk_log > w + 1 => {
            rtl_gkr_quotient_sumcheck_prove_packed_br_base(
                prover_state,
                nums,
                dens,
                *chunk_log,
                &claim_point.0,
                alpha,
                expected_sum,
            )
        }
        LayerStorage::PackedBrBase { nums, dens, chunk_log } => {
            let n_nat: Vec<EF> = unpack_base_and_unreverse::<EF>(nums, *chunk_log)
                .into_iter()
                .map(EF::from)
                .collect();
            let d_nat = unpack_and_unreverse::<EF>(dens, *chunk_log);
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
        LayerStorage::PackedBr { nums, dens, chunk_log } if *chunk_log > w + 1 => {
            rtl_gkr_quotient_sumcheck_prove_packed_br(
                prover_state,
                nums,
                dens,
                *chunk_log,
                &claim_point.0,
                alpha,
                expected_sum,
            )
        }
        LayerStorage::PackedBr { nums, dens, chunk_log } => {
            let n_nat = unpack_and_unreverse::<EF>(nums, *chunk_log);
            let d_nat = unpack_and_unreverse::<EF>(dens, *chunk_log);
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
        LayerStorage::Natural { nums, dens } => {
            let (num_l, num_r) = even_odd_split(nums);
            let (den_l, den_r) = even_odd_split(dens);
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

    let nl_q = inner_evals[0];
    let nr_q = inner_evals[1];
    let dl_q = inner_evals[2];
    let dr_q = inner_evals[3];

    let one_minus_beta = EF::ONE - beta;
    let next_num = one_minus_beta * nl_q + beta * nr_q;
    let next_den = one_minus_beta * dl_q + beta * dr_q;

    // q_natural has K coords; new layer's claim point is q || [β] (β is the
    // new LSB, i.e. the X_K that was just reduced from the parent layer).
    q_natural.push(beta);
    (MultilinearPoint(q_natural), next_num, next_den)
}

// Runs a right-to-left sumcheck proving:
//   expected_sum = Σ_{b ∈ {0,1}^K} eq(b, eq_point)
//                   · [num_l(b)·den_r(b) + num_r(b)·den_l(b) + α · den_l(b)·den_r(b)]
//
// Each of `num_l, num_r, den_l, den_r` is a K-variable MLE stored in
// lexicographic order (its LSB = X_{K-1}).  We bind the LSB in round 0, the
// new LSB in round 1, and so on, until K challenges have been sampled.
//
// Returns (q, [num_l(q), num_r(q), den_l(q), den_r(q)]) where `q` is in
// natural order (x_0, ..., x_{K-1}).
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
    let k = eq_point.len();
    debug_assert_eq!(num_l.len(), 1 << k);
    debug_assert_eq!(num_r.len(), 1 << k);
    debug_assert_eq!(den_l.len(), 1 << k);
    debug_assert_eq!(den_r.len(), 1 << k);

    let remaining_eq: Vec<EF> = eq_point.to_vec();
    let q_natural: Vec<EF> = Vec::with_capacity(k);
    rtl_gkr_quotient_sumcheck_prove_unpacked_rounds(
        prover_state,
        num_l,
        num_r,
        den_l,
        den_r,
        remaining_eq,
        q_natural,
        alpha,
        expected_sum,
        EF::ONE,
    )
}

// Unpacked phase of the sumcheck.  `remaining_eq` is the still-to-be-bound
// suffix of the original eq_point; the caller may have already consumed its
// tail in phase 1.  `q_natural` collects prepended challenges in natural order
// (round r prepends at index 0 so the final layout is `[r_{K-1}, …, r_0]`).
//
// Invariant entering the round:
//   sum = mmf · H_r(x_0 = r_0, …, x_{r-1} = r_{r-1})
//   mmf = Π_{i<r} eq(α_i, r_i)
// The bare polynomial we send is mmf · H_r(z); the `Some(eq_alpha)` back-loaded
// batching then tracks target *= eq(eq_alpha, r) each round on the verifier.
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
        let eq_prefix: &[EF] = &remaining_eq[..remaining_eq.len() - 1];
        let eq_table: Vec<EF> = if eq_prefix.is_empty() {
            vec![EF::ONE]
        } else {
            eval_eq(eq_prefix)
        };

        let half = num_l.len() / 2; // number of LSB pairs
        debug_assert_eq!(eq_table.len(), half);

        // H(z) = Σ_j eq_table[j] · [ NL(j,z) · DR(j,z) + NR(j,z) · DL(j,z)
        //                           + α · DL(j,z) · DR(j,z) ]
        // where NL(j,z) = num_l[2j] + z·(num_l[2j+1] - num_l[2j]), etc.
        // H has degree 2; evaluate at z=0 and z=2, reconstruct z=1 from sum
        // constraint.
        // 4 separate accumulators: (c0_s, c2_s) for the α-coupled DL·DR term,
        // (c0_d, c2_d) for the double (NL·DR + NR·DL) term. α is applied once
        // per round at finalize, saving two scalar mults per pair.
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

            let nl_d = nl1 - nl0;
            let nr_d = nr1 - nr0;
            let dl_d = dl1 - dl0;
            let dr_d = dr1 - dr0;

            // (u·v) coefficients: c0 = u0·v0, c2 = (u1−u0)·(v1−v0).
            let c0_s = dl0 * dr0;
            let c2_s = dl_d * dr_d;
            let c0_d = nl0 * dr0 + nr0 * dl0;
            let c2_d = nl_d * dr_d + nr_d * dl_d;

            let eq = eq_table[j];
            c0_s_raw += eq * c0_s;
            c2_s_raw += eq * c2_s;
            c0_d_raw += eq * c0_d;
            c2_d_raw += eq * c2_d;
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

        // Next round's sum = full(r) = eq(eq_alpha, r) · h(r).
        let eq_eval = (EF::ONE - eq_alpha) * (EF::ONE - r) + eq_alpha * r;
        sum = eq_eval * bare.evaluate(r);
        mmf *= eq_eval;

        num_l = fold_lsb(&num_l, r);
        num_r = fold_lsb(&num_r, r);
        den_l = fold_lsb(&den_l, r);
        den_r = fold_lsb(&den_r, r);

        q_natural.insert(0, r);
        remaining_eq.pop();
    }

    debug_assert_eq!(num_l.len(), 1);
    let evals = [num_l[0], num_r[0], den_l[0], den_r[0]];
    (q_natural, evals)
}

// Phase-1 SIMD sumcheck for a packed-BR parent layer. Splits the parent into
// four K-variable MLEs (L/R for num, den) in packed-BR with chunk_log =
// parent_chunk_log - 1, then runs as many SIMD rounds as possible (each round
// folds at the current chunk-MSB packed bit). When the next fold would cross
// the lane boundary, we unpack + un-bit-reverse and hand off to the unpacked
// round loop. The transcript is identical to the unpacked variant.
//
// Three optimizations vs. the naive per-round eval_eq+bit-reverse+pack:
//   - SplitEq: eq table stays factorized as `eq_lo × eq_hi_packed`, so building
//     it costs O(sqrt(2^n)) instead of O(2^n) per round.
//   - Fused fold + compute: from round 1 onward, the fold from round r-1 and
//     the compute for round r share a single pass over the arrays (reads each
//     packed word once instead of twice).
//   - Per-round permuted_alphas matches the bit-reversed storage, so SplitEq's
//     packed-index access maps directly onto our chunk-aware pair stride.
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

    // Hand off the combined layer directly — borrow the layer's slices; we
    // only allocate when the first fused round produces new arrays.
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

/// Phase-1 sumcheck for the biggest layer, where numerators are still in the
/// base field (`PFPacking`). Runs round 0 as base × ext (full base-field
/// density), then folds nums → EFPacking and continues the normal ext-only
/// path via `run_phase1_packed`.
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
    // Outer bits above `parent_chunk_log` (combined view includes the sibling bit).
    let head_len = (k + 1).saturating_sub(parent_chunk_log);
    let mut q_natural: Vec<EF> = Vec::with_capacity(k);
    let mut mmf = EF::ONE;
    let mut sum = expected_sum;

    // eq_outer is invariant across all phase-1 rounds — build once.
    let eq_outer: Vec<EF> = if head_len == 0 {
        vec![EF::ONE]
    } else {
        eval_eq(&remaining_eq[..head_len])
    };

    // --- Round 0: compute h_0 on base × ext directly on the combined layer. ---
    let eq_alpha_0 = *remaining_eq.last().unwrap();
    let within_pt_0: Vec<EF> =
        remaining_eq[head_len..remaining_eq.len() - 1].iter().rev().copied().collect();
    let eq_within_0 = eval_eq_packed(&within_pt_0);

    let (c0_s_pkg, c2_s_pkg, c0_d_pkg, c2_d_pkg) = compute_round_base_ext(
        packed_nums,
        packed_dens,
        parent_chunk_log,
        &eq_outer,
        &eq_within_0,
    );

    // α applied once per round (not per pair).
    let c0_raw: EF = EFPacking::<EF>::to_ext_iter([c0_d_pkg + c0_s_pkg * alpha]).sum::<EF>();
    let c2_raw: EF = EFPacking::<EF>::to_ext_iter([c2_d_pkg + c2_s_pkg * alpha]).sum::<EF>();
    let bare_0 = build_bare_from_coeffs(c0_raw, c2_raw, eq_alpha_0, sum, mmf);
    prover_state.add_sumcheck_polynomial(&bare_0.coeffs, Some(eq_alpha_0));
    let r0: EF = prover_state.sample();
    let eq_eval_0 = (EF::ONE - eq_alpha_0) * (EF::ONE - r0) + eq_alpha_0 * r0;
    sum = eq_eval_0 * bare_0.evaluate(r0);
    mmf *= eq_eval_0;
    q_natural.insert(0, r0);
    remaining_eq.pop();

    // --- Round 1 FUSED: fold base→ext with r0 AND compute round-1 poly. ---
    //
    // If `parent_chunk_log < w + 3` we can't fuse (the fused helper needs
    // three packed bits: sib, prev=r0, cur=round-1 fold). That only happens
    // in tiny edge cases — fall back to the non-fused path.
    if parent_chunk_log >= w + 3 && remaining_eq.len() > w + 1 {
        let eq_alpha_1 = *remaining_eq.last().unwrap();
        let within_pt_1: Vec<EF> =
            remaining_eq[head_len..remaining_eq.len() - 1].iter().rev().copied().collect();
        let eq_within_1 = eval_eq_packed(&within_pt_1);

        let (nums_ext, dens_ext, c0_s_1, c2_s_1, c0_d_1, c2_d_1) =
            fold_and_compute_round_packed_base_to_ext::<EF>(
                packed_nums,
                packed_dens,
                parent_chunk_log,
                r0,
                &eq_outer,
                &eq_within_1,
            );

        let c0_r1: EF = EFPacking::<EF>::to_ext_iter([c0_d_1 + c0_s_1 * alpha]).sum::<EF>();
        let c2_r1: EF = EFPacking::<EF>::to_ext_iter([c2_d_1 + c2_s_1 * alpha]).sum::<EF>();
        let bare_1 = build_bare_from_coeffs(c0_r1, c2_r1, eq_alpha_1, sum, mmf);
        prover_state.add_sumcheck_polynomial(&bare_1.coeffs, Some(eq_alpha_1));
        let r1: EF = prover_state.sample();
        let eq_eval_1 = (EF::ONE - eq_alpha_1) * (EF::ONE - r1) + eq_alpha_1 * r1;
        sum = eq_eval_1 * bare_1.evaluate(r1);
        mmf *= eq_eval_1;
        q_natural.insert(0, r1);
        remaining_eq.pop();

        // `nums_ext`/`dens_ext` are at `chunk_log = parent_chunk_log - 1`
        // (round 0 fold applied, round 1 fold still pending via r1).  Hand
        // off to `run_phase1_packed` with the pending_r set so its first
        // iteration absorbs r1 into a fused round-2 compute.
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
        // Fallback: do the round-0 fold as a separate pass.  Only reachable
        // when the layer is tiny; not exercised on the xmss hot path.
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

/// Run phase-1 rounds. Does non-fused compute on round 0 (no pending fold),
/// then fuses fold-from-previous + compute-for-current on subsequent rounds.
/// Transitions to the unpacked loop when chunks shrink to one packed word or
/// SplitEq can no longer stay in packed mode.
/// Combined-view phase-1 SIMD sumcheck.  `nums`/`dens` are the FULL layer
/// arrays at `layer_chunk_log` — the L/R sibling bit is stored at the
/// chunk-MSB, so the first half of each parent chunk is L, the second half is
/// R.  No `split_packed_br_by_chunk_msb` allocation.
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
    // Optional pending fold to apply in the first fused iteration. Used by
    // `_base` when it has manually run round 1 via
    // `fold_and_compute_round_packed_base_to_ext` and the sampled challenge
    // still needs to be absorbed into `nums`/`dens` before round 2's compute.
    initial_pending_r: Option<EF>,
) -> (Vec<EF>, [EF; 4]) {
    let w = packing_log_width::<EF>();
    let k_initial = remaining_eq.len();
    // Outer bits (above `layer_chunk_log`, plus the sibling bit which lives
    // intra-chunk in combined view): head_len = K+1 − layer_chunk_log.
    let head_len = (k_initial + 1).saturating_sub(layer_chunk_log);

    // eq_outer is derived from `remaining_eq[..head_len]`, which is INVARIANT
    // across phase-1 rounds (we only pop the tail each round). Build once.
    let eq_outer: Vec<EF> = precomputed_eq_outer.unwrap_or_else(|| {
        if head_len == 0 {
            vec![EF::ONE]
        } else {
            eval_eq(&remaining_eq[..head_len])
        }
    });

    // Fused fold + compute loop.  Round 0 falls back to unfused compute (no
    // `pending_r` yet); subsequent rounds fuse the prev fold with the current
    // compute in a single sweep.
    //
    // The non-fused compute needs `layer_chunk_log ≥ w + 2` (sib + fold bits
    // both in packed space); the fused variant needs `layer_chunk_log ≥ w + 3`
    // (sib + prev + cur bits). The loop guard `layer_chunk_log > w + 1`
    // ensures the non-fused bound; the fused bound is implicitly satisfied
    // because `pending_r` is only set after a round that increments the
    // requirement by 1 at the next iteration.
    let mut pending_r: Option<EF> = initial_pending_r;
    while layer_chunk_log > w + 1 && remaining_eq.len() > w + 1 {
        let eq_alpha = *remaining_eq.last().unwrap();
        // eq_within shrinks by one variable each round; rebuild it (small,
        // fits in one packed word at small layer_chunk_log).
        let within_pt: Vec<EF> =
            remaining_eq[head_len..remaining_eq.len() - 1].iter().rev().copied().collect();
        let eq_within = eval_eq_packed(&within_pt);

        let (c0_s_pkg, c2_s_pkg, c0_d_pkg, c2_d_pkg) = if let Some(prev_r) = pending_r.take() {
            // Input is still at the pre-fold `layer_chunk_log + 1`.
            let (new_nums, new_dens, c0s, c2s, c0d, c2d) = fold_and_compute_round_packed(
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
            compute_round_packed(nums.as_ref(), dens.as_ref(), layer_chunk_log, &eq_outer, &eq_within)
        };

        // α is applied once per round here, not per pair.
        let c0_raw: EF = EFPacking::<EF>::to_ext_iter([c0_d_pkg + c0_s_pkg * alpha]).sum::<EF>();
        let c2_raw: EF = EFPacking::<EF>::to_ext_iter([c2_d_pkg + c2_s_pkg * alpha]).sum::<EF>();
        let bare = build_bare_from_coeffs(c0_raw, c2_raw, eq_alpha, sum, mmf);
        prover_state.add_sumcheck_polynomial(&bare.coeffs, Some(eq_alpha));
        let r = prover_state.sample();
        let eq_eval = (EF::ONE - eq_alpha) * (EF::ONE - r) + eq_alpha * r;
        sum = eq_eval * bare.evaluate(r);
        mmf *= eq_eval;

        pending_r = Some(r);
        layer_chunk_log -= 1;
        q_natural.insert(0, r);
        remaining_eq.pop();
    }

    // Apply any pending fold before exiting the packed path.  Input arrays
    // are still at `layer_chunk_log + 1`; the round's fold bit is the sib+1
    // bit, storage bit `layer_chunk_log - 1`, packed bit `layer_chunk_log-1-w`.
    if let Some(prev_r) = pending_r.take() {
        let prev_bit = layer_chunk_log - 1 - w;
        nums = Cow::Owned(fold_multilinear_at_bit(nums.as_ref(), prev_r, prev_bit, &|v, a| v * a));
        dens = Cow::Owned(fold_multilinear_at_bit(dens.as_ref(), prev_r, prev_bit, &|v, a| v * a));
    }

    // Transition to phase 2: unpack + un-bit-reverse the combined array, then
    // even/odd-split to produce L/R sides.  Sib bit in packed-BR is natural
    // LSB (storage chunk-MSB ↔ natural bit 0), so L = even-indexed,
    // R = odd-indexed in natural order.
    let nums_nat = unpack_and_unreverse::<EF>(nums.as_ref(), layer_chunk_log);
    let dens_nat = unpack_and_unreverse::<EF>(dens.as_ref(), layer_chunk_log);
    let (num_l_nat, num_r_nat) = even_odd_split(&nums_nat);
    let (den_l_nat, den_r_nat) = even_odd_split(&dens_nat);

    rtl_gkr_quotient_sumcheck_prove_unpacked_rounds(
        prover_state,
        num_l_nat,
        num_r_nat,
        den_l_nat,
        den_r_nat,
        remaining_eq,
        q_natural,
        alpha,
        sum,
        mmf,
    )
}

/// Compute (h(0), h(2)) of one phase-1 round polynomial on packed-BR arrays.
///
/// Iterates outer-chunk first (so the scalar `eq_outer[chunk]` is applied once
/// per chunk instead of once per pair), then within-chunk pairs. The pair bit
/// is the chunk-MSB at the given chunk_log, so within a chunk the pair is at
/// positions `(i0, i0 + chunk_packed/2)` — cache-contiguous.
/// Combined-view round-0 compute on packed-BR arrays.  `nums`/`dens` are the
/// UNSPLIT layer data at `layer_chunk_log`; within each parent chunk the
/// first half is the L side and the second half is R.  Returns the 4
/// accumulators `(c0_s, c2_s, c0_d, c2_d)`.
#[allow(clippy::too_many_arguments)]
fn compute_round_packed<EF: ExtensionField<PF<EF>>>(
    nums: &[EFPacking<EF>],
    dens: &[EFPacking<EF>],
    layer_chunk_log: usize,
    eq_outer: &[EF],
    eq_within: &[EFPacking<EF>],
) -> (EFPacking<EF>, EFPacking<EF>, EFPacking<EF>, EFPacking<EF>) {
    let w = packing_log_width::<EF>();
    debug_assert!(layer_chunk_log >= w + 2);
    let layer_packed = 1usize << (layer_chunk_log - w);
    let half = layer_packed / 2; // L/R sibling stride within chunk
    let quarter = layer_packed / 4; // fold stride within each side
    debug_assert!(nums.len().is_multiple_of(layer_packed));
    debug_assert_eq!(nums.len() / layer_packed, eq_outer.len().max(1));
    debug_assert_eq!(eq_within.len(), quarter);

    type P<EF> = EFPacking<EF>;
    let zero = || (P::<EF>::ZERO, P::<EF>::ZERO, P::<EF>::ZERO, P::<EF>::ZERO);
    let add = |a: (P<EF>, P<EF>, P<EF>, P<EF>), b: (P<EF>, P<EF>, P<EF>, P<EF>)| {
        (a.0 + b.0, a.1 + b.1, a.2 + b.2, a.3 + b.3)
    };

    nums.par_chunks_exact(layer_packed)
        .zip(dens.par_chunks_exact(layer_packed))
        .enumerate()
        .fold(zero, |mut acc, (c, (n_c, d_c))| {
            let eq_o: EF = eq_outer.get(c).copied().unwrap_or(EF::ONE);
            let (mut l_c0s, mut l_c2s, mut l_c0d, mut l_c2d) =
                (P::<EF>::ZERO, P::<EF>::ZERO, P::<EF>::ZERO, P::<EF>::ZERO);
            for inner in 0..quarter {
                let nl0 = n_c[inner];
                let nl1 = n_c[inner + quarter];
                let nr0 = n_c[inner + half];
                let nr1 = n_c[inner + half + quarter];
                let dl0 = d_c[inner];
                let dl1 = d_c[inner + quarter];
                let dr0 = d_c[inner + half];
                let dr1 = d_c[inner + half + quarter];

                let (c0_s, c2_s) = sumcheck_quadratic_pair(&dl0, &dl1, &dr0, &dr1);
                let (c0_a, c2_a) = sumcheck_quadratic_pair(&nl0, &nl1, &dr0, &dr1);
                let (c0_b, c2_b) = sumcheck_quadratic_pair(&nr0, &nr1, &dl0, &dl1);
                let eq_w = eq_within[inner];
                l_c0s += c0_s * eq_w;
                l_c2s += c2_s * eq_w;
                l_c0d += (c0_a + c0_b) * eq_w;
                l_c2d += (c2_a + c2_b) * eq_w;
            }
            acc.0 += l_c0s * eq_o;
            acc.1 += l_c2s * eq_o;
            acc.2 += l_c0d * eq_o;
            acc.3 += l_c2d * eq_o;
            acc
        })
        .reduce(zero, add)
}

/// Base × ext variant of `compute_round_packed` for round 0 of the biggest
/// sumcheck, where numerators are still in `PFPacking`.  Combined view —
/// `nums`/`dens` are the full layer data at `layer_chunk_log`.
#[allow(clippy::too_many_arguments)]
fn compute_round_base_ext<EF: ExtensionField<PF<EF>>>(
    nums: &[PFPacking<EF>],
    dens: &[EFPacking<EF>],
    layer_chunk_log: usize,
    eq_outer: &[EF],
    eq_within: &[EFPacking<EF>],
) -> (EFPacking<EF>, EFPacking<EF>, EFPacking<EF>, EFPacking<EF>)
where
    EFPacking<EF>: Algebra<PFPacking<EF>>,
{
    let w = packing_log_width::<EF>();
    debug_assert!(layer_chunk_log >= w + 2);
    let layer_packed = 1usize << (layer_chunk_log - w);
    let half = layer_packed / 2;
    let quarter = layer_packed / 4;
    debug_assert!(nums.len().is_multiple_of(layer_packed));
    debug_assert_eq!(eq_within.len(), quarter);

    type P<EF> = EFPacking<EF>;
    let zero = || (P::<EF>::ZERO, P::<EF>::ZERO, P::<EF>::ZERO, P::<EF>::ZERO);
    let add = |a: (P<EF>, P<EF>, P<EF>, P<EF>), b: (P<EF>, P<EF>, P<EF>, P<EF>)| {
        (a.0 + b.0, a.1 + b.1, a.2 + b.2, a.3 + b.3)
    };

    nums.par_chunks_exact(layer_packed)
        .zip(dens.par_chunks_exact(layer_packed))
        .enumerate()
        .fold(zero, |mut acc, (c, (n_c, d_c))| {
            let eq_o: EF = eq_outer.get(c).copied().unwrap_or(EF::ONE);
            let (mut l_c0s, mut l_c2s, mut l_c0d, mut l_c2d) =
                (P::<EF>::ZERO, P::<EF>::ZERO, P::<EF>::ZERO, P::<EF>::ZERO);
            for inner in 0..quarter {
                let nl0 = n_c[inner];
                let nl1 = n_c[inner + quarter];
                let nr0 = n_c[inner + half];
                let nr1 = n_c[inner + half + quarter];
                let dl0 = d_c[inner];
                let dl1 = d_c[inner + quarter];
                let dr0 = d_c[inner + half];
                let dr1 = d_c[inner + half + quarter];

                let (c0_s, c2_s) = sumcheck_quadratic_pair(&dl0, &dl1, &dr0, &dr1);
                let (c0_a, c2_a) = sumcheck_quadratic_base_ext::<EF>(&nl0, &nl1, &dr0, &dr1);
                let (c0_b, c2_b) = sumcheck_quadratic_base_ext::<EF>(&nr0, &nr1, &dl0, &dl1);
                let eq_w = eq_within[inner];
                l_c0s += c0_s * eq_w;
                l_c2s += c2_s * eq_w;
                l_c0d += (c0_a + c0_b) * eq_w;
                l_c2d += (c2_a + c2_b) * eq_w;
            }
            acc.0 += l_c0s * eq_o;
            acc.1 += l_c2s * eq_o;
            acc.2 += l_c0d * eq_o;
            acc.3 += l_c2d * eq_o;
            acc
        })
        .reduce(zero, add)
}

/// Build the outer (scalar EF, per-chunk) and within (packed EF, per pair)
/// equality tables for this round. The split is precisely at the chunk-index
/// vs. within-chunk boundary — the outer table is applied once per chunk in
/// the loop, the within table once per pair.
fn build_outer_within_eq<EF: ExtensionField<PF<EF>>>(
    eq_prefix: &[EF],
    head_len: usize,
) -> (Vec<EF>, Vec<EFPacking<EF>>) {
    let outer_eq_pt = &eq_prefix[..head_len];
    // Within-chunk variables are stored bit-reversed, so the eq points are in
    // reverse natural order.
    let within_eq_pt: Vec<EF> = eq_prefix[head_len..].iter().rev().copied().collect();
    let eq_outer = if outer_eq_pt.is_empty() {
        vec![EF::ONE]
    } else {
        eval_eq(outer_eq_pt)
    };
    let eq_within_packed = eval_eq_packed(&within_eq_pt);
    (eq_outer, eq_within_packed)
}

/// Fused round for phase-1: apply the prev-round fold to the four packed-BR
/// arrays AND compute the next round polynomial in a single pass.
///
/// Iterates outer-chunk first (amortized `eq_outer[c]` scalar per chunk),
/// inner pair within the chunk. Within each input chunk of 2^(chunk_log_old -
/// w) packed elements, the prev-fold bit is the top bit and the compute-fold
/// bit is one below — matching the standard `(i, i+half)` / `(i, i+quarter)`
/// four-way access pattern. Output arrays have `chunk_log_old - 1` chunk_log
/// and half the packed length.
/// Combined-view fused fold + compute. `nums`/`dens` are at `layer_chunk_log_old`;
/// within each parent chunk the first half is the L side and the second half
/// is R. Writes the fold-output as new combined arrays at
/// `layer_chunk_log_old - 1`, preserving the same "L first, R second" in-chunk
/// layout. Returns `(new_nums, new_dens, c0_s, c2_s, c0_d, c2_d)`.
#[allow(clippy::too_many_arguments, clippy::type_complexity)]
fn fold_and_compute_round_packed<EF: ExtensionField<PF<EF>>>(
    nums: &[EFPacking<EF>],
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
) {
    let w = packing_log_width::<EF>();
    debug_assert!(layer_chunk_log_old >= w + 3);
    let in_packed = 1usize << (layer_chunk_log_old - w);
    let in_half = in_packed / 2; // L/R sibling stride in input
    let in_quarter = in_packed / 4; // prev fold stride in input
    let in_eighth = in_packed / 8; // cur fold stride in input
    let out_packed = in_packed / 2; // new chunk size
    let out_half = out_packed / 2; // = in_quarter; L/R stride in output
    let out_quarter = out_packed / 4; // = in_eighth; cur fold stride in output
    debug_assert!(nums.len().is_multiple_of(in_packed));
    debug_assert_eq!(eq_within.len(), in_eighth);

    let new_len = nums.len() / 2;
    let mut new_nums: Vec<EFPacking<EF>> = unsafe { uninitialized_vec(new_len) };
    let mut new_dens: Vec<EFPacking<EF>> = unsafe { uninitialized_vec(new_len) };

    type P<EF> = EFPacking<EF>;
    let zero = || (P::<EF>::ZERO, P::<EF>::ZERO, P::<EF>::ZERO, P::<EF>::ZERO);
    let add = |a: (P<EF>, P<EF>, P<EF>, P<EF>), b: (P<EF>, P<EF>, P<EF>, P<EF>)| {
        (a.0 + b.0, a.1 + b.1, a.2 + b.2, a.3 + b.3)
    };

    let (c0s, c2s, c0d, c2d) = nums
        .par_chunks_exact(in_packed)
        .zip(dens.par_chunks_exact(in_packed))
        .zip(new_nums.par_chunks_exact_mut(out_packed))
        .zip(new_dens.par_chunks_exact_mut(out_packed))
        .enumerate()
        .fold(zero, |mut acc, (c, (((n_c, d_c), nn_c), nd_c))| {
            let eq_o: EF = eq_outer.get(c).copied().unwrap_or(EF::ONE);
            let (mut l_c0s, mut l_c2s, mut l_c0d, mut l_c2d) =
                (P::<EF>::ZERO, P::<EF>::ZERO, P::<EF>::ZERO, P::<EF>::ZERO);
            for i in 0..in_eighth {
                // Within input chunk, access by (sib, prev, cur) bits.
                // sib stride = in_half, prev stride = in_quarter, cur stride = in_eighth.
                let l_p0_c0 = i;
                let l_p0_c1 = i + in_eighth;
                let l_p1_c0 = i + in_quarter;
                let l_p1_c1 = i + in_quarter + in_eighth;
                let r_p0_c0 = i + in_half;
                let r_p0_c1 = i + in_half + in_eighth;
                let r_p1_c0 = i + in_half + in_quarter;
                let r_p1_c1 = i + in_half + in_quarter + in_eighth;

                // Fold prev bit with `prev_r` — yields 4 values per-multilinear
                // (L/R × cur=0/1).
                let fl_nl = n_c[l_p0_c0] + (n_c[l_p1_c0] - n_c[l_p0_c0]) * prev_r;
                let fr_nl = n_c[l_p0_c1] + (n_c[l_p1_c1] - n_c[l_p0_c1]) * prev_r;
                let fl_nr = n_c[r_p0_c0] + (n_c[r_p1_c0] - n_c[r_p0_c0]) * prev_r;
                let fr_nr = n_c[r_p0_c1] + (n_c[r_p1_c1] - n_c[r_p0_c1]) * prev_r;
                let fl_dl = d_c[l_p0_c0] + (d_c[l_p1_c0] - d_c[l_p0_c0]) * prev_r;
                let fr_dl = d_c[l_p0_c1] + (d_c[l_p1_c1] - d_c[l_p0_c1]) * prev_r;
                let fl_dr = d_c[r_p0_c0] + (d_c[r_p1_c0] - d_c[r_p0_c0]) * prev_r;
                let fr_dr = d_c[r_p0_c1] + (d_c[r_p1_c1] - d_c[r_p0_c1]) * prev_r;

                // Write to output (sib × cur × inner); sib stride = out_half,
                // cur stride = out_quarter.
                nn_c[i] = fl_nl;
                nn_c[i + out_quarter] = fr_nl;
                nn_c[i + out_half] = fl_nr;
                nn_c[i + out_half + out_quarter] = fr_nr;
                nd_c[i] = fl_dl;
                nd_c[i + out_quarter] = fr_dl;
                nd_c[i + out_half] = fl_dr;
                nd_c[i + out_half + out_quarter] = fr_dr;

                let eq_w = eq_within[i];
                let (c0_s, c2_s) = sumcheck_quadratic_pair(&fl_dl, &fr_dl, &fl_dr, &fr_dr);
                let (c0_a, c2_a) = sumcheck_quadratic_pair(&fl_nl, &fr_nl, &fl_dr, &fr_dr);
                let (c0_b, c2_b) = sumcheck_quadratic_pair(&fl_nr, &fr_nr, &fl_dl, &fr_dl);
                l_c0s += c0_s * eq_w;
                l_c2s += c2_s * eq_w;
                l_c0d += (c0_a + c0_b) * eq_w;
                l_c2d += (c2_a + c2_b) * eq_w;
            }
            acc.0 += l_c0s * eq_o;
            acc.1 += l_c2s * eq_o;
            acc.2 += l_c0d * eq_o;
            acc.3 += l_c2d * eq_o;
            acc
        })
        .reduce(zero, add);

    (new_nums, new_dens, c0s, c2s, c0d, c2d)
}

/// Base-num variant of [`fold_and_compute_round_packed`] — fuses the base→ext
/// fold of `nums` (from `PFPacking` to `EFPacking`) with the round-compute
/// pass.  Used by `rtl_..._packed_br_base` to avoid a separate
/// `fold_base_to_ext_at_bit` + `fold_multilinear_at_bit` pass on the top
/// layer (saves one full-array write + re-read across both multilinears).
#[allow(clippy::too_many_arguments, clippy::type_complexity)]
fn fold_and_compute_round_packed_base_to_ext<EF: ExtensionField<PF<EF>>>(
    nums_base: &[PFPacking<EF>],
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
    EFPacking<EF>: Algebra<PFPacking<EF>>,
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
    debug_assert!(nums_base.len().is_multiple_of(in_packed));
    debug_assert_eq!(dens.len(), nums_base.len());
    debug_assert_eq!(eq_within.len(), in_eighth);

    let new_len = nums_base.len() / 2;
    let mut new_nums: Vec<EFPacking<EF>> = unsafe { uninitialized_vec(new_len) };
    let mut new_dens: Vec<EFPacking<EF>> = unsafe { uninitialized_vec(new_len) };

    // Base fold requires prev_r as EFPacking (PFPacking * EF isn't direct;
    // we use EFPacking * PFPacking via Algebra<PFPacking>).
    let prev_r_packed: EFPacking<EF> = <EFPacking<EF> as From<EF>>::from(prev_r);

    type P<EF> = EFPacking<EF>;
    let zero = || (P::<EF>::ZERO, P::<EF>::ZERO, P::<EF>::ZERO, P::<EF>::ZERO);
    let add = |a: (P<EF>, P<EF>, P<EF>, P<EF>), b: (P<EF>, P<EF>, P<EF>, P<EF>)| {
        (a.0 + b.0, a.1 + b.1, a.2 + b.2, a.3 + b.3)
    };

    let (c0s, c2s, c0d, c2d) = nums_base
        .par_chunks_exact(in_packed)
        .zip(dens.par_chunks_exact(in_packed))
        .zip(new_nums.par_chunks_exact_mut(out_packed))
        .zip(new_dens.par_chunks_exact_mut(out_packed))
        .enumerate()
        .fold(zero, |mut acc, (c, (((n_c, d_c), nn_c), nd_c))| {
            let eq_o: EF = eq_outer.get(c).copied().unwrap_or(EF::ONE);
            let (mut l_c0s, mut l_c2s, mut l_c0d, mut l_c2d) =
                (P::<EF>::ZERO, P::<EF>::ZERO, P::<EF>::ZERO, P::<EF>::ZERO);
            for i in 0..in_eighth {
                let l_p0_c0 = i;
                let l_p0_c1 = i + in_eighth;
                let l_p1_c0 = i + in_quarter;
                let l_p1_c1 = i + in_quarter + in_eighth;
                let r_p0_c0 = i + in_half;
                let r_p0_c1 = i + in_half + in_eighth;
                let r_p1_c0 = i + in_half + in_quarter;
                let r_p1_c1 = i + in_half + in_quarter + in_eighth;

                // Fold base nums: PFPacking → EFPacking.
                let fl_nl: P<EF> = prev_r_packed * (n_c[l_p1_c0] - n_c[l_p0_c0]) + n_c[l_p0_c0];
                let fr_nl: P<EF> = prev_r_packed * (n_c[l_p1_c1] - n_c[l_p0_c1]) + n_c[l_p0_c1];
                let fl_nr: P<EF> = prev_r_packed * (n_c[r_p1_c0] - n_c[r_p0_c0]) + n_c[r_p0_c0];
                let fr_nr: P<EF> = prev_r_packed * (n_c[r_p1_c1] - n_c[r_p0_c1]) + n_c[r_p0_c1];
                // Fold ext dens.
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
                let (c0_s, c2_s) = sumcheck_quadratic_pair(&fl_dl, &fr_dl, &fl_dr, &fr_dr);
                let (c0_a, c2_a) = sumcheck_quadratic_pair(&fl_nl, &fr_nl, &fl_dr, &fr_dr);
                let (c0_b, c2_b) = sumcheck_quadratic_pair(&fl_nr, &fr_nr, &fl_dl, &fr_dl);
                l_c0s += c0_s * eq_w;
                l_c2s += c2_s * eq_w;
                l_c0d += (c0_a + c0_b) * eq_w;
                l_c2d += (c2_a + c2_b) * eq_w;
            }
            acc.0 += l_c0s * eq_o;
            acc.1 += l_c2s * eq_o;
            acc.2 += l_c0d * eq_o;
            acc.3 += l_c2d * eq_o;
            acc
        })
        .reduce(zero, add);

    (new_nums, new_dens, c0s, c2s, c0d, c2d)
}

/// Build the bare round polynomial (scaled by `mmf`) from the z⁰ and z²
/// coefficients of `H(z)`.  h(1) is recovered from the sum constraint, then
/// c1 = h(1) − c0 − c2.
#[inline]
fn build_bare_from_coeffs<EF: ExtensionField<PF<EF>>>(
    c0_raw: EF,
    c2_raw: EF,
    eq_alpha: EF,
    sum: EF,
    mmf: EF,
) -> DensePolynomial<EF> {
    let c0_mmf = c0_raw * mmf;
    let c2_mmf = c2_raw * mmf;
    // sum = (1 − eq_α)·h(0) + eq_α·h(1)  ⇒  h(1) = (sum − (1−eq_α)·c0) / eq_α.
    let h1_mmf = (sum - (EF::ONE - eq_alpha) * c0_mmf) / eq_alpha;
    let c1_mmf = h1_mmf - c0_mmf - c2_mmf;
    DensePolynomial::new(vec![c0_mmf, c1_mmf, c2_mmf])
}

/// Constant (z⁰) and quadratic (z²) coefficients of `(u·v)(z)` where
/// `u(z) = u0 + z·(u1-u0)`, same for `v`. So `const = u0·v0`,
/// `quad = (u1-u0)·(v1-v0)`.  Using the coefficient form avoids the two
/// `double()` ops that the `(2u1-u0)(2v1-v0)` / `h(2)` form needs.
/// Callers must reconstruct the sumcheck polynomial from these coefficients
/// (directly, via `DensePolynomial::new`) instead of from `(h(0), h(2))`.
#[inline(always)]
fn sumcheck_quadratic_pair<A: Copy + PrimeCharacteristicRing>(u0: &A, u1: &A, v0: &A, v1: &A) -> (A, A) {
    let c0 = *u0 * *v0;
    let u_diff = *u1 - *u0;
    let v_diff = *v1 - *v0;
    let c2 = u_diff * v_diff;
    (c0, c2)
}

/// Same as `sumcheck_quadratic_pair` but the first factor is base-field
/// packed; the output is extension-field packed (via `Algebra<N>` on
/// `EFPacking`). Returns (z⁰ coef, z² coef).
#[inline(always)]
fn sumcheck_quadratic_base_ext<EF: ExtensionField<PF<EF>>>(
    u0: &PFPacking<EF>,
    u1: &PFPacking<EF>,
    v0: &EFPacking<EF>,
    v1: &EFPacking<EF>,
) -> (EFPacking<EF>, EFPacking<EF>)
where
    EFPacking<EF>: Algebra<PFPacking<EF>>,
{
    let c0 = *v0 * *u0;
    let u_diff = *u1 - *u0;
    let v_diff = *v1 - *v0;
    let c2 = v_diff * u_diff;
    (c0, c2)
}

/// Fold a base-field-packed array at `bit`, producing an extension-field
/// packed result. `a * alpha` uses `EFPacking: Algebra<PFPacking>`.
fn fold_base_to_ext_at_bit<EF: ExtensionField<PF<EF>>>(m: &[PFPacking<EF>], alpha: EF, bit: usize) -> Vec<EFPacking<EF>>
where
    EFPacking<EF>: Algebra<PFPacking<EF>>,
{
    let alpha_packed: EFPacking<EF> = <EFPacking<EF> as From<EF>>::from(alpha);
    let new_size = m.len() / 2;
    let stride = 1usize << bit;
    let lo_mask = stride - 1;
    let mut res = unsafe { uninitialized_vec(new_size) };
    let compute = |new_j: usize| -> EFPacking<EF> {
        let i_hi = new_j >> bit;
        let i_lo = new_j & lo_mask;
        let i0 = (i_hi << (bit + 1)) | i_lo;
        let i1 = i0 | stride;
        // m[i1] - m[i0] is base-field packed; alpha_packed * diff_base uses
        // EFPacking's Algebra<PFPacking> to lift into the extension field.
        let diff_base = m[i1] - m[i0];
        alpha_packed * diff_base + m[i0]
    };
    if new_size < PARALLEL_THRESHOLD {
        for (new_j, out) in res.iter_mut().enumerate() {
            *out = compute(new_j);
        }
    } else {
        (0..new_size)
            .into_par_iter()
            .with_min_len(PARALLEL_THRESHOLD)
            .map(compute)
            .collect_into_vec(&mut res);
    }
    res
}

pub fn verify_gkr_quotient<EF: ExtensionField<PF<EF>>>(
    verifier_state: &mut impl FSVerifier<EF>,
    n_vars: usize,
) -> Result<(EF, MultilinearPoint<EF>, EF, EF), ProofError> {
    assert!(n_vars > N_VARS_TO_SEND_GKR_COEFFS);
    let send_len = 1 << N_VARS_TO_SEND_GKR_COEFFS;
    let top_nums = verifier_state.next_extension_scalars_vec(send_len)?;
    let top_dens = verifier_state.next_extension_scalars_vec(send_len)?;
    let quotient = compute_quotient(&top_nums, &top_dens);

    let mut point = MultilinearPoint(verifier_state.sample_vec(N_VARS_TO_SEND_GKR_COEFFS));
    let mut claim_num = top_nums.evaluate(&point);
    let mut claim_den = top_dens.evaluate(&point);

    for k in N_VARS_TO_SEND_GKR_COEFFS..n_vars {
        let (next_point, next_num, next_den) =
            verify_gkr_quotient_step(verifier_state, k, &point, claim_num, claim_den)?;
        point = next_point;
        claim_num = next_num;
        claim_den = next_den;
    }

    Ok((quotient, point, claim_num, claim_den))
}

fn verify_gkr_quotient_step<EF: ExtensionField<PF<EF>>>(
    verifier_state: &mut impl FSVerifier<EF>,
    k: usize,
    claim_point: &MultilinearPoint<EF>,
    claim_num: EF,
    claim_den: EF,
) -> Result<(MultilinearPoint<EF>, EF, EF), ProofError> {
    let alpha = verifier_state.sample();
    let expected_sum = claim_num + alpha * claim_den;

    let (q_natural, final_target) = rtl_gkr_quotient_sumcheck_verify(verifier_state, k, &claim_point.0, expected_sum)?;

    let inner_evals = verifier_state.next_extension_scalars_vec(4)?;
    let nl_q = inner_evals[0];
    let nr_q = inner_evals[1];
    let dl_q = inner_evals[2];
    let dr_q = inner_evals[3];

    let q_point = MultilinearPoint(q_natural.clone());
    let eq_factor = claim_point.eq_poly_outside(&q_point);
    let expected = eq_factor * (nl_q * dr_q + nr_q * dl_q + alpha * dl_q * dr_q);
    if final_target != expected {
        return Err(ProofError::InvalidProof);
    }

    let beta = verifier_state.sample();
    let one_minus_beta = EF::ONE - beta;
    let next_num = one_minus_beta * nl_q + beta * nr_q;
    let next_den = one_minus_beta * dl_q + beta * dr_q;

    let mut next_point = q_natural;
    next_point.push(beta);
    Ok((MultilinearPoint(next_point), next_num, next_den))
}

// Mirror of rtl_gkr_quotient_sumcheck_prove: walks eq_point from the back, one
// eq_alpha per round. Returns (q_natural, final_running_target) — the target
// the caller must then cross-check against the inner_evals.
fn rtl_gkr_quotient_sumcheck_verify<EF: ExtensionField<PF<EF>>>(
    verifier_state: &mut impl FSVerifier<EF>,
    k: usize,
    eq_point: &[EF],
    initial_sum: EF,
) -> Result<(Vec<EF>, EF), ProofError> {
    debug_assert_eq!(eq_point.len(), k);
    let mut target = initial_sum;
    let mut q_natural: Vec<EF> = Vec::with_capacity(k);
    for round in 0..k {
        let eq_alpha = eq_point[k - 1 - round];
        let coeffs = verifier_state.next_sumcheck_polynomial(4, target, Some(eq_alpha))?;
        let pol = DensePolynomial::new(coeffs);
        let r = verifier_state.sample();
        target = pol.evaluate(r);
        q_natural.insert(0, r);
    }
    Ok((q_natural, target))
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

fn mle_ref_to_vec_ef<EF: ExtensionField<PF<EF>>>(mle: &MleRef<'_, EF>) -> Vec<EF> {
    match mle {
        MleRef::Base(v) => v.iter().map(|&x| EF::from(x)).collect(),
        MleRef::Extension(v) => v.to_vec(),
        MleRef::BasePacked(pb) => PFPacking::<EF>::unpack_slice(pb).iter().map(|&x| EF::from(x)).collect(),
        MleRef::ExtensionPacked(ep) => unpack_extension_fast::<EF>(ep),
    }
}

fn even_odd_split<EF: Copy>(v: &[EF]) -> (Vec<EF>, Vec<EF>) {
    let half = v.len() / 2;
    let mut l = Vec::with_capacity(half);
    let mut r = Vec::with_capacity(half);
    for i in 0..half {
        l.push(v[2 * i]);
        r.push(v[2 * i + 1]);
    }
    (l, r)
}

fn fold_lsb<EF: ExtensionField<PF<EF>>>(u: &[EF], r: EF) -> Vec<EF> {
    (0..u.len() / 2)
        .map(|j| u[2 * j] + r * (u[2 * j + 1] - u[2 * j]))
        .collect()
}

/// Takes a natural-order Vec<EF> of size 2^N, bit-reverses each chunk of size
/// 2^chunk_log (requires chunk_log >= packing_log_width), and returns the
/// resulting data packed into Vec<EFPacking<EF>>.
pub fn bit_reverse_chunks_and_pack<EF: ExtensionField<PF<EF>>>(v: &[EF], chunk_log: usize) -> Vec<EFPacking<EF>> {
    let n = v.len();
    debug_assert!(n.is_power_of_two());
    debug_assert!(chunk_log <= n.trailing_zeros() as usize);
    let chunk_size = 1usize << chunk_log;
    let shift = usize::BITS as usize - chunk_log;

    // Bit-reverse each chunk in an unpacked buffer, then pack.
    let mut reordered: Vec<EF> = unsafe { uninitialized_vec(n) };
    reordered
        .par_chunks_exact_mut(chunk_size)
        .zip(v.par_chunks_exact(chunk_size))
        .for_each(|(dst, src)| {
            for (p, slot) in dst.iter_mut().enumerate() {
                *slot = src[p.reverse_bits() >> shift];
            }
        });
    pack_extension(&reordered)
}

/// Inverse of `bit_reverse_chunks_and_pack`: unpack the `EFPacking` slice and
/// un-bit-reverse each chunk of size 2^chunk_log, giving a natural-order
/// Vec<EF>. When `chunk_log == 0`, this is just an unpack.
fn unpack_and_unreverse<EF: ExtensionField<PF<EF>>>(v: &[EFPacking<EF>], chunk_log: usize) -> Vec<EF> {
    let unpacked: Vec<EF> = unpack_extension_fast::<EF>(v);
    if chunk_log == 0 {
        return unpacked;
    }
    let n = unpacked.len();
    let chunk_size = 1usize << chunk_log;
    let shift = usize::BITS as usize - chunk_log;
    let mut out: Vec<EF> = unsafe { uninitialized_vec(n) };
    out.par_chunks_exact_mut(chunk_size)
        .zip(unpacked.par_chunks_exact(chunk_size))
        .for_each(|(dst, src)| {
            // bit-reversal is an involution, so the inverse is bit-reversal.
            for (p, slot) in dst.iter_mut().enumerate() {
                *slot = src[p.reverse_bits() >> shift];
            }
        });
    out
}

/// GKR layer reduction on packed bit-reversed data. Folds the chunk-MSB
/// (storage bit `chunk_log - 1`), which in packed space is packed-index bit
/// `chunk_log - 1 - w`. Requires `chunk_log > w` so that the pair lives in
/// different packed words (fully SIMD, no within-lane work).
///
/// Output is again packed + bit-reversed, with chunk size `2^(chunk_log - 1)`.
fn sum_quotients_packed_br<EF: ExtensionField<PF<EF>>>(
    nums: &[EFPacking<EF>],
    dens: &[EFPacking<EF>],
    chunk_log: usize,
) -> (Vec<EFPacking<EF>>, Vec<EFPacking<EF>>) {
    let w = packing_log_width::<EF>();
    debug_assert!(chunk_log > w);
    debug_assert_eq!(nums.len(), dens.len());

    let bit = chunk_log - 1 - w; // packed-index bit to fold
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
            let n0 = nums[i0];
            let n1 = nums[i1];
            let d0 = dens[i0];
            let d1 = dens[i1];
            *num_out = d1 * n0 + d0 * n1;
            *den_out = d0 * d1;
        });

    (new_nums, new_dens)
}

/// Base-field variant of `sum_quotients_packed_br`: nums in `PFPacking`, dens
/// in `EFPacking`, outputs are both `EFPacking`.
fn sum_quotients_packed_br_base<EF: ExtensionField<PF<EF>>>(
    nums: &[PFPacking<EF>],
    dens: &[EFPacking<EF>],
    chunk_log: usize,
) -> (Vec<EFPacking<EF>>, Vec<EFPacking<EF>>)
where
    EFPacking<EF>: Algebra<PFPacking<EF>>,
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
            let n0 = nums[i0];
            let n1 = nums[i1];
            let d0 = dens[i0];
            let d1 = dens[i1];
            *num_out = d1 * n0 + d0 * n1;
            *den_out = d0 * d1;
        });

    (new_nums, new_dens)
}

/// Base-field variant of `bit_reverse_chunks_and_pack`.
pub fn bit_reverse_chunks_and_pack_base<EF: ExtensionField<PF<EF>>>(
    v: &[PF<EF>],
    chunk_log: usize,
) -> Vec<PFPacking<EF>> {
    let n = v.len();
    debug_assert!(n.is_power_of_two());
    debug_assert!(chunk_log <= n.trailing_zeros() as usize);
    let chunk_size = 1usize << chunk_log;
    let shift = usize::BITS as usize - chunk_log;

    let mut reordered: Vec<PF<EF>> = unsafe { uninitialized_vec(n) };
    reordered
        .par_chunks_exact_mut(chunk_size)
        .zip(v.par_chunks_exact(chunk_size))
        .for_each(|(dst, src)| {
            for (p, slot) in dst.iter_mut().enumerate() {
                *slot = src[p.reverse_bits() >> shift];
            }
        });
    // Pack into PFPacking.
    let width = packing_width::<EF>();
    reordered
        .par_chunks_exact(width)
        .map(|chunk| {
            let slice: &[PF<EF>] = chunk;
            *PFPacking::<EF>::from_slice(slice)
        })
        .collect()
}

/// Fast unpack for `EFPacking`: writes directly into a pre-allocated output
/// buffer, avoiding the per-packed-word `Vec` allocation that the default
/// `unpack_extension` does. For an 80MB output this is the difference between
/// ~300 ms and ~10 ms on our hot path.
pub fn unpack_extension_fast<EF: ExtensionField<PF<EF>>>(v: &[EFPacking<EF>]) -> Vec<EF> {
    let width = packing_width::<EF>();
    let total = v.len() * width;
    let mut out: Vec<EF> = unsafe { uninitialized_vec(total) };
    let write = |out_chunk: &mut [EF], x: &EFPacking<EF>| {
        let packed_coeffs = x.as_basis_coefficients_slice();
        for (lane, slot) in out_chunk.iter_mut().enumerate() {
            *slot = EF::from_basis_coefficients_fn(|j| packed_coeffs[j].as_slice()[lane]);
        }
    };
    if total < PARALLEL_THRESHOLD {
        for (chunk, x) in out.chunks_exact_mut(width).zip(v.iter()) {
            write(chunk, x);
        }
    } else {
        out.par_chunks_exact_mut(width)
            .zip(v.par_iter())
            .for_each(|(chunk, x)| write(chunk, x));
    }
    out
}

/// Base-field variant of `unpack_and_unreverse`.
fn unpack_base_and_unreverse<EF: ExtensionField<PF<EF>>>(v: &[PFPacking<EF>], chunk_log: usize) -> Vec<PF<EF>> {
    let unpacked: Vec<PF<EF>> = PFPacking::<EF>::unpack_slice(v).to_vec();
    if chunk_log == 0 {
        return unpacked;
    }
    let n = unpacked.len();
    let chunk_size = 1usize << chunk_log;
    let shift = usize::BITS as usize - chunk_log;
    let mut out: Vec<PF<EF>> = unsafe { uninitialized_vec(n) };
    out.par_chunks_exact_mut(chunk_size)
        .zip(unpacked.par_chunks_exact(chunk_size))
        .for_each(|(dst, src)| {
            for (p, slot) in dst.iter_mut().enumerate() {
                *slot = src[p.reverse_bits() >> shift];
            }
        });
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{RngExt, SeedableRng, rngs::StdRng};
    use std::time::Instant;
    use utils::{build_prover_state, build_verifier_state, init_tracing};

    type F = KoalaBear;
    type EF = QuinticExtensionFieldKB;

    fn sum_all_quotients(nums: &[F], den: &[EF]) -> EF {
        nums.par_iter().zip(den).map(|(&n, &d)| EF::from(n) / d).sum()
    }

    fn run_roundtrip(log_n: usize) {
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

        let prover_statements =
            prove_gkr_quotient::<EF>(&mut prover_state, &numerators.by_ref(), &denominators.by_ref());

        let mut verifier_state = build_verifier_state(prover_state).unwrap();
        let verifier_statements = verify_gkr_quotient::<EF>(&mut verifier_state, log_n).unwrap();
        assert_eq!(&verifier_statements, &prover_statements);
        let (retrieved_quotient, claim_point, claim_num, claim_den) = verifier_statements;
        assert_eq!(retrieved_quotient, real_quotient);
        assert_eq!(numerators.evaluate(&claim_point), claim_num);
        assert_eq!(denominators.evaluate(&claim_point), claim_den);
    }

    #[test]
    fn test_gkr_quotient() {
        init_tracing();
        let log_n = 13;
        let time = Instant::now();
        run_roundtrip(log_n);
        println!("Proving time (log_n={log_n}): {:?}", time.elapsed());
    }

    #[test]
    #[ignore]
    fn bench_gkr_quotient() {
        init_tracing();
        for log_n in [18, 20, 22] {
            let time = Instant::now();
            run_roundtrip(log_n);
            println!("Proving time (log_n={log_n}): {:?}", time.elapsed());
        }
    }

    // Exercise the phase-1 → phase-2 boundary for several small sizes. These
    // sit near the pivot (`ENDIANNESS_PIVOT = 12`) so the packed phase-1 runs
    // for a handful of rounds before the sumcheck transitions to unpacked.
    #[test]
    fn test_gkr_quotient_phase1_boundary() {
        for log_n in [9, 10, 11, 12, 13] {
            run_roundtrip(log_n);
        }
    }
}
