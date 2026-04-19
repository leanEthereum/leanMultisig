use backend::*;

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
        let mut h0_raw = EF::ZERO;
        let mut h2_raw = EF::ZERO;
        for j in 0..half {
            let nl0 = num_l[2 * j];
            let nl1 = num_l[2 * j + 1];
            let nr0 = num_r[2 * j];
            let nr1 = num_r[2 * j + 1];
            let dl0 = den_l[2 * j];
            let dl1 = den_l[2 * j + 1];
            let dr0 = den_r[2 * j];
            let dr1 = den_r[2 * j + 1];

            let inner0 = nl0 * dr0 + nr0 * dl0 + alpha * dl0 * dr0;

            let nl2 = nl1.double() - nl0;
            let nr2 = nr1.double() - nr0;
            let dl2 = dl1.double() - dl0;
            let dr2 = dr1.double() - dr0;
            let inner2 = nl2 * dr2 + nr2 * dl2 + alpha * dl2 * dr2;

            h0_raw += eq_table[j] * inner0;
            h2_raw += eq_table[j] * inner2;
        }

        let h0 = h0_raw * mmf;
        let h2 = h2_raw * mmf;

        // sum = (1 - eq_alpha)·h(0) + eq_alpha·h(1)
        let h1 = (sum - (EF::ONE - eq_alpha) * h0) / eq_alpha;

        let bare = DensePolynomial::lagrange_interpolation(&[
            (PF::<EF>::ZERO, h0),
            (PF::<EF>::ONE, h1),
            (PF::<EF>::from_usize(2), h2),
        ])
        .unwrap();

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

    let (num_l, num_r) = split_packed_br_by_chunk_msb::<EF>(packed_nums, parent_chunk_log);
    let (den_l, den_r) = split_packed_br_by_chunk_msb::<EF>(packed_dens, parent_chunk_log);
    let initial_chunk_log = parent_chunk_log - 1;

    run_phase1_packed(
        prover_state,
        num_l,
        num_r,
        den_l,
        den_r,
        initial_chunk_log,
        eq_point.to_vec(),
        Vec::with_capacity(eq_point.len()),
        alpha,
        expected_sum,
        EF::ONE,
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

    let (num_l_base, num_r_base) = split_packed_br_by_chunk_msb_base::<EF>(packed_nums, parent_chunk_log);
    let (den_l, den_r) = split_packed_br_by_chunk_msb::<EF>(packed_dens, parent_chunk_log);
    let initial_chunk_log = parent_chunk_log - 1;

    let k = eq_point.len();
    let mut remaining_eq = eq_point.to_vec();
    let head_len = k.saturating_sub(initial_chunk_log);
    let mut q_natural: Vec<EF> = Vec::with_capacity(k);
    let mut mmf = EF::ONE;
    let mut sum = expected_sum;

    // Round 0: compute h_0 on base × ext. After sampling r_0, the fold
    // promotes numerators to EFPacking so the rest of phase 1 runs ext × ext.
    let eq_alpha = *remaining_eq.last().unwrap();
    let eq_prefix: &[EF] = &remaining_eq[..remaining_eq.len() - 1];
    let (eq_outer, eq_within) = build_outer_within_eq::<EF>(eq_prefix, head_len);

    let (h0_pkg, h2_pkg) = compute_round_base_ext(
        &num_l_base,
        &num_r_base,
        &den_l,
        &den_r,
        initial_chunk_log,
        alpha,
        &eq_outer,
        &eq_within,
    );

    let h0_raw: EF = EFPacking::<EF>::to_ext_iter([h0_pkg]).sum::<EF>();
    let h2_raw: EF = EFPacking::<EF>::to_ext_iter([h2_pkg]).sum::<EF>();
    let h0 = h0_raw * mmf;
    let h2 = h2_raw * mmf;
    let h1 = (sum - (EF::ONE - eq_alpha) * h0) / eq_alpha;
    let bare = DensePolynomial::lagrange_interpolation(&[
        (PF::<EF>::ZERO, h0),
        (PF::<EF>::ONE, h1),
        (PF::<EF>::from_usize(2), h2),
    ])
    .unwrap();
    prover_state.add_sumcheck_polynomial(&bare.coeffs, Some(eq_alpha));
    let r0: EF = prover_state.sample();
    let eq_eval = (EF::ONE - eq_alpha) * (EF::ONE - r0) + eq_alpha * r0;
    sum = eq_eval * bare.evaluate(r0);
    mmf *= eq_eval;
    q_natural.insert(0, r0);
    remaining_eq.pop();

    // Fold base nums + ext dens into ext-only arrays using r_0.
    let fold_bit = initial_chunk_log - 1 - w;
    let num_l = fold_base_to_ext_at_bit::<EF>(&num_l_base, r0, fold_bit);
    let num_r = fold_base_to_ext_at_bit::<EF>(&num_r_base, r0, fold_bit);
    let den_l = fold_multilinear_at_bit(&den_l, r0, fold_bit, &|v, a| v * a);
    let den_r = fold_multilinear_at_bit(&den_r, r0, fold_bit, &|v, a| v * a);

    run_phase1_packed(
        prover_state,
        num_l,
        num_r,
        den_l,
        den_r,
        initial_chunk_log - 1,
        remaining_eq,
        q_natural,
        alpha,
        sum,
        mmf,
    )
}

/// Run phase-1 rounds. Does non-fused compute on round 0 (no pending fold),
/// then fuses fold-from-previous + compute-for-current on subsequent rounds.
/// Transitions to the unpacked loop when chunks shrink to one packed word or
/// SplitEq can no longer stay in packed mode.
#[allow(clippy::too_many_arguments)]
fn run_phase1_packed<EF: ExtensionField<PF<EF>>>(
    prover_state: &mut impl FSProver<EF>,
    mut num_l: Vec<EFPacking<EF>>,
    mut num_r: Vec<EFPacking<EF>>,
    mut den_l: Vec<EFPacking<EF>>,
    mut den_r: Vec<EFPacking<EF>>,
    mut chunk_log: usize,
    mut remaining_eq: Vec<EF>,
    mut q_natural: Vec<EF>,
    alpha: EF,
    mut sum: EF,
    mut mmf: EF,
) -> (Vec<EF>, [EF; 4]) {
    let w = packing_log_width::<EF>();
    // eq_prefix length threshold to keep SplitEq in packed mode.
    // Also need chunk_log > w so that the NEXT pair fold stays out of lane.
    let k_initial = remaining_eq.len();
    let head_len = k_initial.saturating_sub(chunk_log);

    // Fused fold + compute loop.  At round r >= 1 we combine the fold from
    // round r-1 (using `pending_r`) with the compute for round r — one sweep
    // over the packed arrays instead of two.  Round 0 and the tail after the
    // final phase-1 round fall back to the unfused path.
    //
    // Exit when either (a) chunks are down to one packed word so the next
    // fold would go within-lane, or (b) SplitEq can no longer stay in packed
    // mode — which needs the eq_prefix length (= remaining_eq.len() - 1) to
    // be strictly greater than w.
    let mut pending_r: Option<EF> = None;
    while chunk_log > w && remaining_eq.len() > w + 1 {
        let eq_alpha = *remaining_eq.last().unwrap();
        let eq_prefix: &[EF] = &remaining_eq[..remaining_eq.len() - 1];
        // Factorize eq: outer over the K-r-chunk_log MSB variables (one scalar
        // per chunk, amortized across the inner loop), within over the
        // chunk_log-1 remaining within-chunk variables (one packed lookup per
        // pair, inside the tight inner loop).
        let (eq_outer, eq_within) = build_outer_within_eq::<EF>(eq_prefix, head_len);

        let (h0_pkg, h2_pkg) = if let Some(prev_r) = pending_r.take() {
            // Fused: apply prev_r fold to arrays at chunk_log+1 AND compute
            // h_r on the resulting size-halved arrays in one pass.
            let (new_nl, new_nr, new_dl, new_dr, h0, h2) = fold_and_compute_round_packed(
                &num_l,
                &num_r,
                &den_l,
                &den_r,
                chunk_log + 1,
                prev_r,
                alpha,
                &eq_outer,
                &eq_within,
            );
            num_l = new_nl;
            num_r = new_nr;
            den_l = new_dl;
            den_r = new_dr;
            (h0, h2)
        } else {
            compute_round_packed(&num_l, &num_r, &den_l, &den_r, chunk_log, alpha, &eq_outer, &eq_within)
        };

        let h0_raw: EF = EFPacking::<EF>::to_ext_iter([h0_pkg]).sum::<EF>();
        let h2_raw: EF = EFPacking::<EF>::to_ext_iter([h2_pkg]).sum::<EF>();
        let h0 = h0_raw * mmf;
        let h2 = h2_raw * mmf;
        let h1 = (sum - (EF::ONE - eq_alpha) * h0) / eq_alpha;
        let bare = DensePolynomial::lagrange_interpolation(&[
            (PF::<EF>::ZERO, h0),
            (PF::<EF>::ONE, h1),
            (PF::<EF>::from_usize(2), h2),
        ])
        .unwrap();
        prover_state.add_sumcheck_polynomial(&bare.coeffs, Some(eq_alpha));
        let r = prover_state.sample();
        let eq_eval = (EF::ONE - eq_alpha) * (EF::ONE - r) + eq_alpha * r;
        sum = eq_eval * bare.evaluate(r);
        mmf *= eq_eval;

        // Don't fold yet — stash r for fusing into the next round.
        pending_r = Some(r);
        chunk_log -= 1;
        q_natural.insert(0, r);
        remaining_eq.pop();
    }

    // Apply any pending fold before exiting the packed path.
    if let Some(prev_r) = pending_r.take() {
        let prev_bit = chunk_log - w; // the bit we folded at when we stashed pending_r
        num_l = fold_multilinear_at_bit(&num_l, prev_r, prev_bit, &|v, a| v * a);
        num_r = fold_multilinear_at_bit(&num_r, prev_r, prev_bit, &|v, a| v * a);
        den_l = fold_multilinear_at_bit(&den_l, prev_r, prev_bit, &|v, a| v * a);
        den_r = fold_multilinear_at_bit(&den_r, prev_r, prev_bit, &|v, a| v * a);
    }

    // Transition to phase 2.
    let num_l_nat = unpack_and_unreverse::<EF>(&num_l, chunk_log);
    let num_r_nat = unpack_and_unreverse::<EF>(&num_r, chunk_log);
    let den_l_nat = unpack_and_unreverse::<EF>(&den_l, chunk_log);
    let den_r_nat = unpack_and_unreverse::<EF>(&den_r, chunk_log);

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
#[allow(clippy::too_many_arguments)]
fn compute_round_packed<EF: ExtensionField<PF<EF>>>(
    num_l: &[EFPacking<EF>],
    num_r: &[EFPacking<EF>],
    den_l: &[EFPacking<EF>],
    den_r: &[EFPacking<EF>],
    chunk_log: usize,
    alpha: EF,
    eq_outer: &[EF],
    eq_within: &[EFPacking<EF>],
) -> (EFPacking<EF>, EFPacking<EF>) {
    let w = packing_log_width::<EF>();
    let chunk_packed = 1usize << (chunk_log - w);
    let half = chunk_packed / 2;
    debug_assert!(num_l.len().is_multiple_of(chunk_packed));
    debug_assert_eq!(num_l.len() / chunk_packed, eq_outer.len().max(1));
    debug_assert_eq!(eq_within.len(), half);

    num_l
        .par_chunks_exact(chunk_packed)
        .zip(num_r.par_chunks_exact(chunk_packed))
        .zip(den_l.par_chunks_exact(chunk_packed))
        .zip(den_r.par_chunks_exact(chunk_packed))
        .enumerate()
        .fold(
            || (EFPacking::<EF>::ZERO, EFPacking::<EF>::ZERO),
            |(mut acc0, mut acc2), (c, (((nl_c, nr_c), dl_c), dr_c))| {
                let eq_o: EF = eq_outer.get(c).copied().unwrap_or(EF::ONE);
                let mut loc0 = EFPacking::<EF>::ZERO;
                let mut loc2 = EFPacking::<EF>::ZERO;
                for inner in 0..half {
                    let i1 = inner + half;
                    let nl0 = nl_c[inner];
                    let nl1 = nl_c[i1];
                    let nr0 = nr_c[inner];
                    let nr1 = nr_c[i1];
                    let dl0 = dl_c[inner];
                    let dl1 = dl_c[i1];
                    let dr0 = dr_c[inner];
                    let dr1 = dr_c[i1];

                    let (t0_s, t2_s) = sumcheck_quadratic_pair(&dl0, &dl1, &dr0, &dr1);
                    let (t0_a, t2_a) = sumcheck_quadratic_pair(&nl0, &nl1, &dr0, &dr1);
                    let (t0_b, t2_b) = sumcheck_quadratic_pair(&nr0, &nr1, &dl0, &dl1);
                    let t0 = (t0_a + t0_b) + t0_s * alpha;
                    let t2 = (t2_a + t2_b) + t2_s * alpha;
                    let eq_w = eq_within[inner];
                    loc0 += t0 * eq_w;
                    loc2 += t2 * eq_w;
                }
                acc0 += loc0 * eq_o;
                acc2 += loc2 * eq_o;
                (acc0, acc2)
            },
        )
        .reduce(
            || (EFPacking::<EF>::ZERO, EFPacking::<EF>::ZERO),
            |(a0, a2), (b0, b2)| (a0 + b0, a2 + b2),
        )
}

/// Base × ext variant of `compute_round_packed` for round 0 of the biggest
/// sumcheck, where numerators are still in `PFPacking`.
#[allow(clippy::too_many_arguments)]
fn compute_round_base_ext<EF: ExtensionField<PF<EF>>>(
    num_l: &[PFPacking<EF>],
    num_r: &[PFPacking<EF>],
    den_l: &[EFPacking<EF>],
    den_r: &[EFPacking<EF>],
    chunk_log: usize,
    alpha: EF,
    eq_outer: &[EF],
    eq_within: &[EFPacking<EF>],
) -> (EFPacking<EF>, EFPacking<EF>)
where
    EFPacking<EF>: Algebra<PFPacking<EF>>,
{
    let w = packing_log_width::<EF>();
    let chunk_packed = 1usize << (chunk_log - w);
    let half = chunk_packed / 2;
    debug_assert!(num_l.len().is_multiple_of(chunk_packed));
    debug_assert_eq!(eq_within.len(), half);

    num_l
        .par_chunks_exact(chunk_packed)
        .zip(num_r.par_chunks_exact(chunk_packed))
        .zip(den_l.par_chunks_exact(chunk_packed))
        .zip(den_r.par_chunks_exact(chunk_packed))
        .enumerate()
        .fold(
            || (EFPacking::<EF>::ZERO, EFPacking::<EF>::ZERO),
            |(mut acc0, mut acc2), (c, (((nl_c, nr_c), dl_c), dr_c))| {
                let eq_o: EF = eq_outer.get(c).copied().unwrap_or(EF::ONE);
                let mut loc0 = EFPacking::<EF>::ZERO;
                let mut loc2 = EFPacking::<EF>::ZERO;
                for inner in 0..half {
                    let i1 = inner + half;
                    let nl0 = nl_c[inner];
                    let nl1 = nl_c[i1];
                    let nr0 = nr_c[inner];
                    let nr1 = nr_c[i1];
                    let dl0 = dl_c[inner];
                    let dl1 = dl_c[i1];
                    let dr0 = dr_c[inner];
                    let dr1 = dr_c[i1];

                    let (t0_s, t2_s) = sumcheck_quadratic_pair(&dl0, &dl1, &dr0, &dr1);
                    let (t0_a, t2_a) = sumcheck_quadratic_base_ext::<EF>(&nl0, &nl1, &dr0, &dr1);
                    let (t0_b, t2_b) = sumcheck_quadratic_base_ext::<EF>(&nr0, &nr1, &dl0, &dl1);
                    let t0 = (t0_a + t0_b) + t0_s * alpha;
                    let t2 = (t2_a + t2_b) + t2_s * alpha;
                    let eq_w = eq_within[inner];
                    loc0 += t0 * eq_w;
                    loc2 += t2 * eq_w;
                }
                acc0 += loc0 * eq_o;
                acc2 += loc2 * eq_o;
                (acc0, acc2)
            },
        )
        .reduce(
            || (EFPacking::<EF>::ZERO, EFPacking::<EF>::ZERO),
            |(a0, a2), (b0, b2)| (a0 + b0, a2 + b2),
        )
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
#[allow(clippy::too_many_arguments, clippy::type_complexity)]
fn fold_and_compute_round_packed<EF: ExtensionField<PF<EF>>>(
    num_l: &[EFPacking<EF>],
    num_r: &[EFPacking<EF>],
    den_l: &[EFPacking<EF>],
    den_r: &[EFPacking<EF>],
    chunk_log_old: usize,
    prev_r: EF,
    alpha: EF,
    eq_outer: &[EF],
    eq_within: &[EFPacking<EF>],
) -> (
    Vec<EFPacking<EF>>,
    Vec<EFPacking<EF>>,
    Vec<EFPacking<EF>>,
    Vec<EFPacking<EF>>,
    EFPacking<EF>,
    EFPacking<EF>,
) {
    let w = packing_log_width::<EF>();
    debug_assert!(chunk_log_old >= w + 2);
    let in_chunk_packed = 1usize << (chunk_log_old - w);
    let out_chunk_packed = in_chunk_packed / 2; // output chunk size
    let half = out_chunk_packed; // stride_prev within input chunk
    let quarter = out_chunk_packed / 2; // stride_cur within input chunk (= output half)
    debug_assert!(num_l.len().is_multiple_of(in_chunk_packed));
    debug_assert_eq!(eq_within.len(), quarter);

    let new_len = num_l.len() / 2;
    let mut new_nl: Vec<EFPacking<EF>> = unsafe { uninitialized_vec(new_len) };
    let mut new_nr: Vec<EFPacking<EF>> = unsafe { uninitialized_vec(new_len) };
    let mut new_dl: Vec<EFPacking<EF>> = unsafe { uninitialized_vec(new_len) };
    let mut new_dr: Vec<EFPacking<EF>> = unsafe { uninitialized_vec(new_len) };

    let (h0_pkg, h2_pkg) = num_l
        .par_chunks_exact(in_chunk_packed)
        .zip(num_r.par_chunks_exact(in_chunk_packed))
        .zip(den_l.par_chunks_exact(in_chunk_packed))
        .zip(den_r.par_chunks_exact(in_chunk_packed))
        .zip(new_nl.par_chunks_exact_mut(out_chunk_packed))
        .zip(new_nr.par_chunks_exact_mut(out_chunk_packed))
        .zip(new_dl.par_chunks_exact_mut(out_chunk_packed))
        .zip(new_dr.par_chunks_exact_mut(out_chunk_packed))
        .enumerate()
        .fold(
            || (EFPacking::<EF>::ZERO, EFPacking::<EF>::ZERO),
            |(mut acc0, mut acc2), (c, (((((((nl_c, nr_c), dl_c), dr_c), o_nl), o_nr), o_dl), o_dr))| {
                let eq_o: EF = eq_outer.get(c).copied().unwrap_or(EF::ONE);
                let mut loc0 = EFPacking::<EF>::ZERO;
                let mut loc2 = EFPacking::<EF>::ZERO;
                for i in 0..quarter {
                    let i_pc01 = i + quarter; // prev=0, cur=1
                    let i_p10 = i + half; // prev=1, cur=0
                    let i_p11 = i_p10 + quarter; // prev=1, cur=1

                    let fl_nl = nl_c[i] + (nl_c[i_p10] - nl_c[i]) * prev_r;
                    let fr_nl = nl_c[i_pc01] + (nl_c[i_p11] - nl_c[i_pc01]) * prev_r;
                    let fl_nr = nr_c[i] + (nr_c[i_p10] - nr_c[i]) * prev_r;
                    let fr_nr = nr_c[i_pc01] + (nr_c[i_p11] - nr_c[i_pc01]) * prev_r;
                    let fl_dl = dl_c[i] + (dl_c[i_p10] - dl_c[i]) * prev_r;
                    let fr_dl = dl_c[i_pc01] + (dl_c[i_p11] - dl_c[i_pc01]) * prev_r;
                    let fl_dr = dr_c[i] + (dr_c[i_p10] - dr_c[i]) * prev_r;
                    let fr_dr = dr_c[i_pc01] + (dr_c[i_p11] - dr_c[i_pc01]) * prev_r;

                    o_nl[i] = fl_nl;
                    o_nl[i + quarter] = fr_nl;
                    o_nr[i] = fl_nr;
                    o_nr[i + quarter] = fr_nr;
                    o_dl[i] = fl_dl;
                    o_dl[i + quarter] = fr_dl;
                    o_dr[i] = fl_dr;
                    o_dr[i + quarter] = fr_dr;

                    let eq_w = eq_within[i];
                    let (t0_s, t2_s) = sumcheck_quadratic_pair(&fl_dl, &fr_dl, &fl_dr, &fr_dr);
                    let (t0_a, t2_a) = sumcheck_quadratic_pair(&fl_nl, &fr_nl, &fl_dr, &fr_dr);
                    let (t0_b, t2_b) = sumcheck_quadratic_pair(&fl_nr, &fr_nr, &fl_dl, &fr_dl);
                    let t0 = (t0_a + t0_b) + t0_s * alpha;
                    let t2 = (t2_a + t2_b) + t2_s * alpha;
                    loc0 += t0 * eq_w;
                    loc2 += t2 * eq_w;
                }
                acc0 += loc0 * eq_o;
                acc2 += loc2 * eq_o;
                (acc0, acc2)
            },
        )
        .reduce(
            || (EFPacking::<EF>::ZERO, EFPacking::<EF>::ZERO),
            |(a0, a2), (b0, b2)| (a0 + b0, a2 + b2),
        );

    (new_nl, new_nr, new_dl, new_dr, h0_pkg, h2_pkg)
}

/// `(u·v)(0), (u·v)(2)` where `u(z) = u0 + z·(u1-u0)`, same for `v`.
/// `(u·v)(0) = u0·v0`, `(u·v)(2) = (2u1-u0)(2v1-v0)`.
#[inline(always)]
fn sumcheck_quadratic_pair<A: Copy + PrimeCharacteristicRing>(u0: &A, u1: &A, v0: &A, v1: &A) -> (A, A) {
    let at0 = *u0 * *v0;
    let u2 = u1.double() - *u0;
    let v2 = v1.double() - *v0;
    let at2 = u2 * v2;
    (at0, at2)
}

/// Same as `sumcheck_quadratic_pair` but the first factor is base-field
/// packed; the output is extension-field packed (via `Algebra<N>` on
/// `EFPacking`).
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
    let at0 = *v0 * *u0;
    let u2 = u1.double() - *u0;
    let v2 = v1.double() - *v0;
    let at2 = v2 * u2;
    (at0, at2)
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

/// Split a packed-BR array by chunk-MSB (which is natural-LSB = 0 vs 1). The
/// first half of each packed chunk becomes L (even natural indices), the
/// second half becomes R (odd). Both outputs are packed-BR with chunk size
/// halved. Requires `parent_chunk_log > w` so the halves are each at least one
/// packed word.
fn split_packed_br_by_chunk_msb<EF: ExtensionField<PF<EF>>>(
    v: &[EFPacking<EF>],
    parent_chunk_log: usize,
) -> (Vec<EFPacking<EF>>, Vec<EFPacking<EF>>) {
    let w = packing_log_width::<EF>();
    debug_assert!(parent_chunk_log > w);
    let parent_chunk_packed = 1usize << (parent_chunk_log - w);
    let half_chunk_packed = parent_chunk_packed / 2;
    debug_assert!(v.len().is_multiple_of(parent_chunk_packed));
    let n_chunks = v.len() / parent_chunk_packed;

    let mut l: Vec<EFPacking<EF>> = unsafe { uninitialized_vec(n_chunks * half_chunk_packed) };
    let mut r: Vec<EFPacking<EF>> = unsafe { uninitialized_vec(n_chunks * half_chunk_packed) };
    l.par_chunks_exact_mut(half_chunk_packed)
        .zip(r.par_chunks_exact_mut(half_chunk_packed))
        .zip(v.par_chunks_exact(parent_chunk_packed))
        .for_each(|((l_dst, r_dst), src)| {
            let (first, second) = src.split_at(half_chunk_packed);
            l_dst.copy_from_slice(first);
            r_dst.copy_from_slice(second);
        });
    (l, r)
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

/// Base-field variant of `split_packed_br_by_chunk_msb`.
fn split_packed_br_by_chunk_msb_base<EF: ExtensionField<PF<EF>>>(
    v: &[PFPacking<EF>],
    parent_chunk_log: usize,
) -> (Vec<PFPacking<EF>>, Vec<PFPacking<EF>>) {
    let w = packing_log_width::<EF>();
    debug_assert!(parent_chunk_log > w);
    let parent_chunk_packed = 1usize << (parent_chunk_log - w);
    let half_chunk_packed = parent_chunk_packed / 2;
    debug_assert!(v.len().is_multiple_of(parent_chunk_packed));
    let n_chunks = v.len() / parent_chunk_packed;

    let mut l: Vec<PFPacking<EF>> = unsafe { uninitialized_vec(n_chunks * half_chunk_packed) };
    let mut r: Vec<PFPacking<EF>> = unsafe { uninitialized_vec(n_chunks * half_chunk_packed) };
    l.par_chunks_exact_mut(half_chunk_packed)
        .zip(r.par_chunks_exact_mut(half_chunk_packed))
        .zip(v.par_chunks_exact(parent_chunk_packed))
        .for_each(|((l_dst, r_dst), src)| {
            let (first, second) = src.split_at(half_chunk_packed);
            l_dst.copy_from_slice(first);
            r_dst.copy_from_slice(second);
        });
    (l, r)
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
