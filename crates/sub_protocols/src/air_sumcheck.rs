use std::collections::BTreeMap;
use std::fmt::Debug;
use std::ops::{Add, AddAssign, Mul, Sub};

use backend::*;
use lean_vm::ColIndex;
use tracing::info_span;

// Sumcheck to prove validity of AIR constraints
//
// 1] We use back-loaded batching (see https://hackmd.io/s/HyxaupAAA)
//
// 2] We fold variables 'right-to-left' (X_{L-1}, X_{L-2}, ..., X_0), but
// use a custom storage layout to keep SIMD on the early rounds (does not
// impact the verifier):
//
// Let L = number of variables, r = current round index (0 ≤ r < L),
// P = min(ENDIANNESS_PIVOT, L), w = packing_log_width (SIMD lane-index bits),
// and "storage-index bit" = the bit of the storage index that round r's
// fold_at_bit targets.
//
// We bit-reverse the storage of each column within chunks of 2^P elements (once, at init).
// The fold schedule has three phases:
//   - Phase 1, rounds [0, P-w): storage-index bit in [w, P), fully SIMD.
//   - Phase 2, rounds [P-w, P): storage-index bit in [0, w), within SIMD-lane, so
//     we unpack before entering this phase.
//   - Phase 3, rounds [P, L): storage-index bit 0 on unpacked storage
// Edge case: when L = P (tables at the minimum size) phase 1 ends one round
// early, at P-w-1, so `SplitEq` stays in packed mode (its eq_point needs length
// > w; at round P-w-1 the eq_point has length L-(P-w-1)-1 = w).

const ENDIANNESS_PIVOT_AIR: usize = 12;

pub trait OuterSumcheckSession<EF: ExtensionField<PF<EF>>>: Debug {
    fn initial_n_vars(&self) -> usize;
    fn sum(&self) -> EF;
    fn bare_degree(&self) -> usize;
    fn eq_alpha(&self) -> EF;
    fn compute_bare_round_poly(&mut self) -> DensePolynomial<EF>;
    fn process_challenge(&mut self, challenge: EF, bare_poly: &DensePolynomial<EF>);
    fn final_column_evals(&self) -> Vec<EF>;
}

#[derive(Debug)]
pub struct AirSumcheckSession<'a, EF: ExtensionField<PF<EF>>, A: Air>
where
    A::ExtraData: AlphaPowers<EF>,
{
    multilinears: MleGroup<'a, EF>,
    eq_factor: Vec<EF>, // The last element is removed at each round
    /// Active element count in the current storage. Always a multiple of
    /// `2^{P - r}` while r < P (chunk-aligned), then ceil-halves afterward.
    current_unpadded_len: usize,
    sum: EF,
    missing_mul_factor: EF,
    computation: A,
    extra_data: A::ExtraData,
    initial_n_vars: usize,
    constraints_eval_at_padding: EF,
    rounds_done: usize,
}

impl<'a, EF: ExtensionField<PF<EF>>, A: Air> AirSumcheckSession<'a, EF, A>
where
    A::ExtraData: AlphaPowers<EF> + AlphaPowersMut<EF>,
{
    pub fn new(
        packed_multilinears: MleGroup<'a, EF>,
        eq_factor: Vec<EF>,
        sum: EF,
        computation: A,
        extra_data: A::ExtraData,
        non_padded_n_rows: usize,
    ) -> Self {
        let initial_n_vars = packed_multilinears.n_vars();
        assert_eq!(eq_factor.len(), initial_n_vars);
        let last_point = column_evals(&packed_multilinears.by_ref(), (1 << initial_n_vars) - 1);
        let constraints_eval_at_padding = A::eval_extension(&computation, &last_point, &extra_data);

        let pivot = ENDIANNESS_PIVOT_AIR.min(initial_n_vars);
        let has_packed_phase = pivot > packing_log_width::<EF>();

        let padded_n_rows = non_padded_n_rows
            .next_multiple_of(1usize << pivot)
            .min(1usize << initial_n_vars);

        let multilinears = match (packed_multilinears.by_ref(), has_packed_phase) {
            (MleGroupRef::BasePacked(cols), true) => {
                let _span = info_span!("chunk-bit-reversing columns").entered();
                let chunk_size = 1usize << pivot;
                let shift = usize::BITS as usize - pivot;
                let bit_reversed = cols
                    .par_iter()
                    .map(|&src| {
                        let mut dst: Vec<PFPacking<EF>> = unsafe { uninitialized_vec(src.len()) };
                        let src_u = PFPacking::<EF>::unpack_slice(src);
                        let dst_u = PFPacking::<EF>::unpack_slice_mut(&mut dst);
                        for (src_chunk, dst_chunk) in
                            src_u.chunks_exact(chunk_size).zip(dst_u.chunks_exact_mut(chunk_size))
                        {
                            for (p, slot) in dst_chunk.iter_mut().enumerate() {
                                *slot = src_chunk[p.reverse_bits() >> shift];
                            }
                        }
                        dst
                    })
                    .collect();
                MleGroup::Owned(MleGroupOwned::BasePacked(bit_reversed))
            }
            _ => unreachable!(),
        };

        Self {
            multilinears,
            eq_factor,
            current_unpadded_len: padded_n_rows,
            sum,
            missing_mul_factor: EF::ONE,
            computation,
            extra_data,
            initial_n_vars,
            constraints_eval_at_padding,
            rounds_done: 0,
        }
    }
}

impl<'a, EF, A> AirSumcheckSession<'a, EF, A>
where
    EF: ExtensionField<PF<EF>>,
    A: Air + 'static,
    A::ExtraData: AlphaPowers<EF>,
{
    fn pivot(&self) -> usize {
        ENDIANNESS_PIVOT_AIR.min(self.initial_n_vars)
    }

    // example:  folding_bit = 2
    // storage (RAM): m[0] m[1] m[2] m[3] m[4] m[5] m[6] m[7]  m[8] m[9] m[10] m[11]  m[12]…
    //                  ╰────┼────┼────┼────╯    │    │    │    ╰──────┼─────┼─────┼─────╯    │
    //                       ╰────┼────┼─────────╯    │    │           ╰─────┼─────┼──────────╯
    //                            ╰────┼──────────────╯    │                 ╰─────┼───────...
    //                                 ╰───────────────────╯                       ╰───────...
    fn folding_bit(&self) -> usize {
        let pivot = self.pivot();
        if self.rounds_done < pivot {
            pivot - 1 - self.rounds_done
        } else {
            0
        }
    }

    // example:  folding_bit_packed = 2, packing_log_width = 3
    // storage (RAM):  m[0..7] m[8..15] m[16..23] m[24..31] m[32..39] m[40..47] m[48..55] m[56..63]  m[64..71] m[72..79] m[80..87] m[88..95]  m[96]…
    //                  ╰──────────┼─────────┼─────────┼─────────╯        │        │        │            ╰───────────┼──────────┼──────────┼──────────╯
    //                             ╰─────────┼─────────┼──────────────────╯        │        │                        ╰──────────┼──────────┼───────...
    //                                       ╰─────────┼───────────────────────────╯        │                                   ╰──────────┼───────...
    //                                                 ╰────────────────────────────────────╯                                              ╰───────...
    fn folding_bit_packed(&self) -> usize {
        let bit = self.folding_bit();
        if self.in_phase_1() {
            bit - packing_log_width::<EF>()
        } else {
            bit
        }
    }

    fn in_phase_1(&self) -> bool {
        let w = packing_log_width::<EF>();
        // (a) the variable being bound sits above the lane bits, and
        // (b) `SplitEq` can still run in packed mode (`n - r - 1 > w`).
        self.rounds_done + w < self.pivot() && self.rounds_done + w + 1 < self.initial_n_vars
    }

    fn active_count_pairs(&self) -> usize {
        if self.in_phase_1() {
            (self.current_unpadded_len / 2) >> packing_log_width::<EF>()
        } else {
            self.current_unpadded_len.div_ceil(2)
        }
    }

    /// `eq_factor` permuted to match our storage convention: entries in
    /// `[0, n-P)` unchanged, entries in `[n-P, len)` reversed
    fn permuted_alphas(&self, len: usize) -> Vec<EF> {
        let head_len = (self.initial_n_vars - self.pivot()).min(len);
        let base = &self.eq_factor[..len];
        let mut out = Vec::with_capacity(len);
        out.extend_from_slice(&base[..head_len]);
        out.extend(base[head_len..].iter().rev().copied());
        out
    }

    /// `C_pad * sum over padded pair positions of partial_eq(new_j)`.
    fn padding_eq_sum(&self, unpadded_len: usize) -> EF {
        let len = self.initial_n_vars - self.rounds_done;
        let mut alphas = self.permuted_alphas(len);
        alphas[len - 1 - self.folding_bit()] = EF::ZERO;
        mle_of_zeros_then_ones(unpadded_len, &alphas)
    }
}

impl<'a, EF, A> OuterSumcheckSession<EF> for AirSumcheckSession<'a, EF, A>
where
    EF: ExtensionField<PF<EF>>,
    A: Air + Debug + 'static,
    A::ExtraData: AlphaPowers<EF> + AlphaPowersMut<EF> + Debug,
{
    fn initial_n_vars(&self) -> usize {
        self.initial_n_vars
    }

    fn sum(&self) -> EF {
        self.sum
    }

    fn bare_degree(&self) -> usize {
        self.computation.degree()
    }

    fn eq_alpha(&self) -> EF {
        *self.eq_factor.last().unwrap()
    }

    fn compute_bare_round_poly(&mut self) -> DensePolynomial<EF> {
        let split_eq = SplitEq::new(&self.permuted_alphas(self.initial_n_vars - self.rounds_done - 1));
        let active_count_pairs = self.active_count_pairs();
        let storage_shift = if self.in_phase_1() {
            packing_log_width::<EF>()
        } else {
            0
        };
        let iter_count_pairs = 1usize << (self.initial_n_vars - self.rounds_done - 1 - storage_shift);
        debug_assert!(active_count_pairs <= iter_count_pairs);

        let padding_contribution = if active_count_pairs < iter_count_pairs {
            self.constraints_eval_at_padding * self.padding_eq_sum(self.current_unpadded_len)
        } else {
            EF::ZERO
        };

        let p_evals_raw = compute_raw_poly(
            &self.multilinears.by_ref(),
            &self.computation,
            &self.extra_data,
            &split_eq,
            self.folding_bit_packed(),
            active_count_pairs,
        );
        let mut p_evals: Vec<EF> = p_evals_raw
            .into_iter()
            .map(|v| (v + padding_contribution) * self.missing_mul_factor)
            .collect();

        let p_at_1 = (self.sum - (EF::ONE - self.eq_alpha()) * p_evals[0]) / self.eq_alpha();
        p_evals.insert(1, p_at_1);

        DensePolynomial::lagrange_interpolation(
            &p_evals
                .iter()
                .enumerate()
                .map(|(i, &val)| (PF::<EF>::from_usize(i), val))
                .collect::<Vec<_>>(),
        )
        .unwrap()
    }

    fn process_challenge(&mut self, challenge: EF, bare_poly: &DensePolynomial<EF>) {
        let alpha_fold = self.eq_alpha();
        let eq_eval = (EF::ONE - alpha_fold) * (EF::ONE - challenge) + alpha_fold * challenge;
        self.sum = bare_poly.evaluate(challenge) * eq_eval;
        self.missing_mul_factor *= eq_eval;

        let was_in_phase_1 = self.in_phase_1();
        let fold_bit = self.folding_bit_packed();

        self.multilinears = self.multilinears.by_ref().fold_at_bit(challenge, fold_bit).into();

        self.current_unpadded_len = self.current_unpadded_len.div_ceil(2);
        self.rounds_done += 1;
        self.eq_factor.pop();

        // Phase 1 → phase 2: unpack
        if was_in_phase_1 && !self.in_phase_1() {
            self.multilinears = self.multilinears.by_ref().unpack().as_owned_or_clone().into();
        }
    }

    fn final_column_evals(&self) -> Vec<EF> {
        column_evals(&self.multilinears.by_ref(), 0)
    }
}

fn column_evals<EF: ExtensionField<PF<EF>>>(multilinears: &MleGroupRef<'_, EF>, i: usize) -> Vec<EF> {
    match multilinears {
        MleGroupRef::Base(cols) => cols.iter().map(|c| EF::from(c[i])).collect(),
        MleGroupRef::Extension(cols) => cols.iter().map(|c| c[i]).collect(),
        MleGroupRef::BasePacked(cols) => {
            let (packed_i, lane) = (i >> packing_log_width::<EF>(), i & (packing_width::<EF>() - 1));
            cols.iter().map(|c| EF::from(c[packed_i].as_slice()[lane])).collect()
        }
        MleGroupRef::ExtensionPacked(cols) => {
            let (packed_i, lane) = (i >> packing_log_width::<EF>(), i & (packing_width::<EF>() - 1));
            cols.iter()
                .map(|c| EFPacking::<EF>::to_ext_iter([c[packed_i]]).nth(lane).unwrap())
                .collect()
        }
    }
}

fn compute_raw_poly<'a, EF, A>(
    multilinears: &MleGroupRef<'a, EF>,
    computation: &A,
    extra_data: &A::ExtraData,
    split_eq: &SplitEq<EF>,
    fold_bit: usize, // in storage
    active_count_pairs: usize,
) -> Vec<EF>
where
    EF: ExtensionField<PF<EF>>,
    A: Air + 'static,
    A::ExtraData: AlphaPowers<EF>,
{
    let unpack_sum_packed = |s: EFPacking<EF>| -> EF { EFPacking::<EF>::to_ext_iter([s]).sum::<EF>() };

    if let Some((low_degree, low_n_constraints)) = computation.low_degree_air() {
        match multilinears {
            MleGroupRef::BasePacked(cols) => {
                return compute_raw_poly_degree_split::<EF, A, PFPacking<EF>, _, _>(
                    cols,
                    |j| split_eq.get_packed(j),
                    computation,
                    extra_data,
                    fold_bit,
                    active_count_pairs,
                    low_degree,
                    low_n_constraints,
                    unpack_sum_packed,
                );
            }
            MleGroupRef::ExtensionPacked(cols) => {
                return compute_raw_poly_degree_split::<EF, A, EFPacking<EF>, _, _>(
                    cols,
                    |j| split_eq.get_packed(j),
                    computation,
                    extra_data,
                    fold_bit,
                    active_count_pairs,
                    low_degree,
                    low_n_constraints,
                    unpack_sum_packed,
                );
            }
            _ => {}
        }
    }

    match multilinears {
        MleGroupRef::BasePacked(cols) => compute_raw_poly_impl::<EF, A, PFPacking<EF>, EFPacking<EF>, _, _>(
            cols,
            |j| split_eq.get_packed(j),
            computation,
            extra_data,
            fold_bit,
            active_count_pairs,
            A::eval_packed_base,
            unpack_sum_packed,
        ),
        MleGroupRef::ExtensionPacked(cols) => compute_raw_poly_impl::<EF, A, EFPacking<EF>, EFPacking<EF>, _, _>(
            cols,
            |j| split_eq.get_packed(j),
            computation,
            extra_data,
            fold_bit,
            active_count_pairs,
            A::eval_packed_extension,
            unpack_sum_packed,
        ),
        MleGroupRef::Base(cols) => compute_raw_poly_impl::<EF, A, PF<EF>, EF, _, _>(
            cols,
            |j| split_eq.get_unpacked(j),
            computation,
            extra_data,
            fold_bit,
            active_count_pairs,
            A::eval_base,
            |s| s,
        ),
        MleGroupRef::Extension(cols) => compute_raw_poly_impl::<EF, A, EF, EF, _, _>(
            cols,
            |j| split_eq.get_unpacked(j),
            computation,
            extra_data,
            fold_bit,
            active_count_pairs,
            A::eval_extension,
            |s| s,
        ),
    }
}

#[allow(clippy::too_many_arguments)]
fn compute_raw_poly_degree_split<EF, A, IF, GetEq, UnpackSum>(
    cols: &[&[IF]],
    get_split_eq: GetEq,
    computation: &A,
    extra_data: &A::ExtraData,
    fold_bit: usize,
    active_count_pairs: usize,
    low_degree: usize,
    low_n_constraints: usize,
    unpack_sum: UnpackSum,
) -> Vec<EF>
where
    EF: ExtensionField<PF<EF>>,
    A: Air + 'static,
    A::ExtraData: AlphaPowers<EF>,
    IF: Algebra<PFPacking<EF>> + Copy + Send + Sync + Sub<Output = IF> + AddAssign + PrimeCharacteristicRing + 'static,
    EFPacking<EF>: PrimeCharacteristicRing
        + Mul<IF, Output = EFPacking<EF>>
        + Add<IF, Output = EFPacking<EF>>
        + Mul<PFPacking<EF>, Output = EFPacking<EF>>,
    GetEq: Fn(usize) -> EFPacking<EF> + Sync + Send,
    UnpackSum: Fn(EFPacking<EF>) -> EF + Sync + Send,
{
    let degree = computation.degree_air();
    let n_cols = cols.len();
    let n_up = computation.n_columns();
    let stride = 1usize << fold_bit;
    let lo_mask = stride - 1;
    let n_full = low_degree + 1;
    let n_skip = degree - n_full;

    // Points where we run the full AIR constraints = {0, 2, 3, …, d_low+1}
    let low_zs: Vec<_> = (std::iter::once(0).chain(2..=(low_degree + 1)).map(PF::<EF>::from_usize)).collect();
    // Points where we skip the low-degree constraints = target_z = {d_low+2, …, degree}
    let hi_zs: Vec<_> = ((low_degree + 2)..=degree).map(PF::<EF>::from_usize).collect();
    let hi_zs_halved: Vec<_> = hi_zs.iter().map(|&tz| tz.halve()).collect();
    let lagrange_coeffs = lagrange_basis_evals(&low_zs, &hi_zs);

    let acc = (0..active_count_pairs)
        .into_par_iter()
        .fold(
            || {
                (
                    vec![EFPacking::<EF>::ZERO; degree],
                    Vec::<IF>::with_capacity(n_cols),
                    Vec::<IF>::with_capacity(n_cols),
                    vec![EFPacking::<EF>::ZERO; n_full],
                    Vec::<IF>::new(),
                    Vec::<IF>::new(),
                    Vec::<IF>::new(),
                )
            },
            |(mut acc, mut point, mut diff, mut low_evals, mut state_0, mut state_2, mut cached_buf), new_j| {
                let i_hi = new_j >> fold_bit;
                let i_lo = new_j & lo_mask;
                let i0 = (i_hi << (fold_bit + 1)) | i_lo;
                let i1 = i0 | stride;
                let partial_eq = get_split_eq(new_j);

                // `point` holds column values at z=0; `diff[k] = col_k[i1] - col_k[i0]`.
                // Invariant for the rest of this closure: `col_k(z) = point[k] + z · diff[k]`,
                // so advancing z by 1 means `point[k] += diff[k]` for all k.
                point.clear();
                diff.clear();
                for c in cols {
                    let lo = c[i0];
                    let hi = c[i1];
                    point.push(lo);
                    diff.push(hi - lo);
                }

                // Phase 1: full AIR constraints

                // z = 0: full eval, capture post-block state.
                {
                    let mut folder = ConstraintFolderPacked::new(&point[..n_up], &point[n_up..], extra_data);
                    folder.cached_state = Some(state_0);
                    Air::eval(computation, &mut folder, extra_data);
                    acc[0] += folder.accumulator * partial_eq;
                    low_evals[0] = folder.accumulator_low;
                    state_0 = folder.cached_state.unwrap();
                }

                // z = 2: advance `point` by 2·diff, full eval, capture post-block state.
                // Together with `state_0` this pins down the linear `state(z)` (linear when we "omit" the low degree constraints of the block)
                for k in 0..n_cols {
                    point[k] += diff[k].double();
                }
                {
                    let mut folder = ConstraintFolderPacked::new(&point[..n_up], &point[n_up..], extra_data);
                    folder.cached_state = Some(state_2);
                    Air::eval(computation, &mut folder, extra_data);
                    acc[1] += folder.accumulator * partial_eq;
                    low_evals[1] = folder.accumulator_low;
                    state_2 = folder.cached_state.unwrap();
                }

                // z = 3, …, d_low+1: still doing full eval
                for z_idx in 2..n_full {
                    for k in 0..n_cols {
                        point[k] += diff[k];
                    }
                    let mut folder = ConstraintFolderPacked::new(&point[..n_up], &point[n_up..], extra_data);
                    Air::eval(computation, &mut folder, extra_data);
                    acc[z_idx] += folder.accumulator * partial_eq;
                    low_evals[z_idx] = folder.accumulator_low;
                }

                // Phase 2: skip the low degree constraints of the block
                // For each skipped point, assemble Constraints(z) = high(z) + low(z):
                //   -high(z): run folder with `skip_low = true`
                //   -low(z): deduce it via Lagrange-interpolation from previous computations
                for t in 0..n_skip {
                    for k in 0..n_cols {
                        point[k] += diff[k];
                    }

                    cached_buf.clear();
                    for i in 0..state_0.len() {
                        cached_buf.push(state_0[i] + (state_2[i] - state_0[i]) * PFPacking::<EF>::from(hi_zs_halved[t]));
                    }

                    let mut folder = ConstraintFolderPacked::new(&point[..n_up], &point[n_up..], extra_data);
                    folder.skip_low = true;
                    folder.cached_state = Some(cached_buf);
                    folder.low_ci_count = low_n_constraints;
                    Air::eval(computation, &mut folder, extra_data);
                    cached_buf = folder.cached_state.unwrap();

                    // low(hi_zs[t]) = Σ_i L_i(hi_zs[t]) · low(low_zs[i])
                    let mut low_interpolated = EFPacking::<EF>::ZERO;
                    for (i, lc) in lagrange_coeffs[t].iter().enumerate() {
                        low_interpolated += low_evals[i] * PFPacking::<EF>::from(*lc);
                    }

                    acc[n_full + t] += (folder.accumulator + low_interpolated) * partial_eq;
                }

                (acc, point, diff, low_evals, state_0, state_2, cached_buf)
            },
        )
        .map(|(acc, ..)| acc)
        .reduce(
            || vec![EFPacking::<EF>::ZERO; degree],
            |mut a, b| {
                for i in 0..degree {
                    a[i] += b[i];
                }
                a
            },
        );

    acc.into_iter().map(&unpack_sum).collect()
}

#[allow(clippy::too_many_arguments)]
fn compute_raw_poly_impl<EF, A, IF, EFT, GetEq, UnpackSum>(
    cols: &[&[IF]],
    get_split_eq: GetEq,
    computation: &A,
    extra_data: &A::ExtraData,
    fold_bit: usize,
    active_count_pairs: usize,
    eval_fn: impl Fn(&A, &[IF], &A::ExtraData) -> EFT + Sync + Send,
    unpack_sum: UnpackSum,
) -> Vec<EF>
where
    EF: ExtensionField<PF<EF>>,
    A: Air + 'static,
    A::ExtraData: AlphaPowers<EF>,
    IF: Copy + Send + Sync + Sub<Output = IF> + AddAssign + PrimeCharacteristicRing,
    EFT: Copy + Send + Sync + Add<Output = EFT> + AddAssign + Mul<Output = EFT> + PrimeCharacteristicRing,
    GetEq: Fn(usize) -> EFT + Sync + Send,
    UnpackSum: Fn(EFT) -> EF + Sync + Send,
{
    let degree = computation.degree();
    let n_cols = cols.len();
    let stride = 1usize << fold_bit;
    let lo_mask = stride - 1;

    let acc = (0..active_count_pairs)
        .into_par_iter()
        .fold(
            || {
                (
                    vec![EFT::ZERO; degree],
                    Vec::<IF>::with_capacity(n_cols),
                    Vec::<IF>::with_capacity(n_cols),
                )
            },
            |(mut acc, mut point, mut diff), new_j| {
                let i_hi = new_j >> fold_bit;
                let i_lo = new_j & lo_mask;
                let i0 = (i_hi << (fold_bit + 1)) | i_lo;
                let i1 = i0 | stride;
                let partial_eq = get_split_eq(new_j);
                point.clear();
                diff.clear();
                for c in cols {
                    let lo = c[i0];
                    let hi = c[i1];
                    point.push(lo);
                    diff.push(hi - lo);
                }
                // z = 0 then (skip z = 1) z = 2, 3, …, degree.
                acc[0] += eval_fn(computation, &point, extra_data) * partial_eq;
                for k in 0..n_cols {
                    point[k] += diff[k];
                }
                for acc_z in &mut acc[1..] {
                    for k in 0..n_cols {
                        point[k] += diff[k];
                    }
                    *acc_z += eval_fn(computation, &point, extra_data) * partial_eq;
                }
                (acc, point, diff)
            },
        )
        .map(|(acc, _, _)| acc)
        .reduce(
            || vec![EFT::ZERO; degree],
            |mut a, b| {
                for i in 0..degree {
                    a[i] += b[i];
                }
                a
            },
        );

    acc.into_iter().map(unpack_sum).collect()
}

pub fn prove_batched_air_sumcheck<'a, EF: ExtensionField<PF<EF>>>(
    prover_state: &mut impl FSProver<EF>,
    sessions: &mut [Box<dyn OuterSumcheckSession<EF> + 'a>],
    eta: EF,
) -> MultilinearPoint<EF> {
    let n_rounds = sessions.iter().map(|s| s.initial_n_vars()).max().unwrap_or(0);
    let max_full_degree = sessions.iter().map(|s| s.bare_degree() + 1).max().unwrap_or(1);
    let eta_powers: Vec<EF> = eta.powers().collect_n(sessions.len());

    let mut challenges = Vec::with_capacity(n_rounds);
    let mut k: Vec<EF> = vec![EF::ONE; sessions.len()];

    for round in 0..n_rounds {
        let mut combined_coeffs = EF::zero_vec(max_full_degree + 1);
        let mut bare_polys: Vec<Option<DensePolynomial<EF>>> = vec![None; sessions.len()];

        for (idx, session) in sessions.iter_mut().enumerate() {
            let join_round = n_rounds - session.initial_n_vars();
            if round < join_round {
                combined_coeffs[1] += eta_powers[idx] * k[idx] * session.sum();
            } else {
                let bare_poly = session.compute_bare_round_poly();
                let full_coeffs = expand_bare_to_full(&bare_poly.coeffs, session.eq_alpha());
                for (i, &c) in full_coeffs.iter().enumerate() {
                    combined_coeffs[i] += eta_powers[idx] * k[idx] * c;
                }
                bare_polys[idx] = Some(bare_poly);
            }
        }

        prover_state.add_sumcheck_polynomial(&combined_coeffs, None);
        let challenge = prover_state.sample();
        challenges.push(challenge);

        for (idx, session) in sessions.iter_mut().enumerate() {
            let join_round = n_rounds - session.initial_n_vars();
            if round < join_round {
                k[idx] *= challenge;
            } else if let Some(bare_poly) = &bare_polys[idx] {
                session.process_challenge(challenge, bare_poly);
            }
        }
    }

    MultilinearPoint(challenges)
}

pub fn compute_shifted_columns<F: Field>(air_down_column_indexes: &[usize], columns: &[&[F]]) -> Vec<Vec<F>> {
    air_down_column_indexes
        .par_iter()
        .map(|&col_index| {
            let column = columns[col_index];
            let mut down = unsafe { uninitialized_vec(column.len()) };
            down[..column.len() - 1].copy_from_slice(&column[1..]);
            down[column.len() - 1] = column[column.len() - 1];
            down
        })
        .collect()
}

pub fn natural_ordering_point_for_session<EF: Copy>(sumcheck_air_point: &[EF], log_n_rows: usize) -> Vec<EF> {
    sumcheck_air_point[sumcheck_air_point.len() - log_n_rows..]
        .iter()
        .rev()
        .copied()
        .collect()
}

pub fn columns_evals_up_and_down<EF: ExtensionField<PF<EF>>, A: Air>(
    air: &A,
    col_evals: &[EF],
    natural_ordering_point: &[EF],
) -> (MultilinearPoint<EF>, BTreeMap<ColIndex, EF>, BTreeMap<ColIndex, EF>) {
    let n_up = air.n_columns();
    debug_assert_eq!(col_evals.len(), n_up + air.n_down_columns());

    let point = MultilinearPoint(natural_ordering_point.to_vec());

    let evals_eq: BTreeMap<ColIndex, EF> = col_evals[..n_up].iter().copied().enumerate().collect();
    let evals_next: BTreeMap<ColIndex, EF> = col_evals[n_up..]
        .iter()
        .zip(air.down_column_indexes())
        .map(|(&v, col_index)| (col_index, v))
        .collect();

    (point, evals_eq, evals_next)
}
