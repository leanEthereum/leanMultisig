use std::collections::BTreeMap;
use std::fmt::Debug;

use backend::*;
use lean_vm::ColIndex;
use rayon::iter::{IntoParallelIterator, ParallelIterator};

// back-loaded batched sumcheck (see https://hackmd.io/s/HyxaupAAA)

pub trait OuterSumcheckSession<EF: ExtensionField<PF<EF>>>: Debug {
    fn initial_n_vars(&self) -> usize;
    fn sum(&self) -> EF;
    fn bare_degree(&self) -> usize;
    fn eq_alpha(&self) -> EF;
    fn compute_bare_round_poly(&mut self) -> DensePolynomial<EF>;
    fn process_challenge(&mut self, challenge: EF, bare_poly: &DensePolynomial<EF>);
    fn final_column_evals(&self) -> Vec<EF>;
}

/// Middle-out folding plan. For a session with `m` variables, the plan folds
/// bit positions in the order [m-p, m-p+1, ..., m-1, m-p-1, m-p-2, ..., 0]
/// where `p = ⌈m/2⌉`. Bits are indexed 0 = LSB, m-1 = MSB. Variables are
/// named X_1 = MSB = bit m-1, X_m = LSB = bit 0; this sequence corresponds to
/// folding X_p, X_{p-1}, ..., X_1, X_{p+1}, ..., X_m.
pub fn middle_out_plan(m: usize) -> Vec<usize> {
    let pivot = m - m.div_ceil(2);
    (pivot..m).chain((0..pivot).rev()).collect()
}

/// Given the overall `sumcheck_air_point` (challenges in fold order) and a
/// per-session fold `plan` of length m, return the session's evaluation
/// point in natural variable order: `result[j-1]` = challenge that bound
/// X_j (i.e. the challenge from the round that folded bit m-1-j).
pub fn natural_point_for_session<EF: Copy>(sumcheck_air_point: &[EF], plan: &[usize]) -> Vec<EF> {
    let m = plan.len();
    let start = sumcheck_air_point.len() - m;
    let mut plan_inverse = vec![0usize; m];
    for (t, &b) in plan.iter().enumerate() {
        plan_inverse[b] = t;
    }
    (0..m)
        .map(|j| sumcheck_air_point[start + plan_inverse[m - 1 - j]])
        .collect()
}

#[derive(Debug)]
pub struct AirSumcheckSession<'a, EF: ExtensionField<PF<EF>>, A: Air>
where
    A::ExtraData: AlphaPowers<EF>,
{
    multilinears: MleGroup<'a, EF>,
    /// Alpha values indexed by ORIGINAL bit position (0 = LSB, m-1 = MSB).
    /// `alpha_by_bit[b]` is the eq_factor alpha for bit b.
    alpha_by_bit: Vec<EF>,
    /// Fold plan: plan[t] = original bit position to fold at round t.
    plan: Vec<usize>,
    /// Currently live original bit positions, sorted ascending. After each
    /// round, the round's fold bit is removed. live_bits.len() == current
    /// n_vars of the MLE storage.
    live_bits: Vec<usize>,
    /// Round index within this session (0-based).
    current_round: usize,
    /// Current unpadded logical length. After each fold, recomputed from the
    /// old length and the fold bit's current position.
    current_unpadded_len: usize,
    /// log_2(packing width) cached for the current MLE representation. 0 if
    /// multilinears is unpacked.
    log_packing: usize,
    sum: EF,
    missing_mul_factors: Option<EF>,
    computation: A,
    extra_data: A::ExtraData,
    initial_n_vars: usize,
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
        // alpha_by_bit[b] = alpha for bit b = eq_factor[m-1-b] (since
        // eq_factor is in natural MSB-first order X_1, X_2, ..., X_m).
        let alpha_by_bit: Vec<EF> = (0..initial_n_vars).map(|b| eq_factor[initial_n_vars - 1 - b]).collect();
        let plan = middle_out_plan(initial_n_vars);
        let live_bits: Vec<usize> = (0..initial_n_vars).collect();
        assert!(packed_multilinears.is_packed());
        let log_packing = packing_log_width::<EF>();
        Self {
            multilinears: packed_multilinears,
            alpha_by_bit,
            plan,
            live_bits,
            current_round: 0,
            current_unpadded_len: non_padded_n_rows,
            log_packing,
            sum,
            missing_mul_factors: None,
            computation,
            extra_data,
            initial_n_vars,
        }
    }

    fn current_fold_bit(&self) -> usize {
        self.plan[self.current_round]
    }

    fn current_fold_position(&self) -> usize {
        self.live_bits
            .iter()
            .position(|&x| x == self.current_fold_bit())
            .unwrap()
    }

    fn compute_eq_others(&self) -> Vec<EF> {
        let fold_bit = self.current_fold_bit();
        // alphas_seq[0] = alpha for MSB (= largest live bit excluding fold_bit).
        let alphas_seq: Vec<EF> = self
            .live_bits
            .iter()
            .rev()
            .filter(|&&b| b != fold_bit)
            .map(|&b| self.alpha_by_bit[b])
            .collect();
        if alphas_seq.is_empty() {
            vec![EF::ONE]
        } else {
            eval_eq(&alphas_seq)
        }
    }

    /// After folding at current-layout position `pos`, return the new unpadded
    /// length in the compact layout (index of the first guaranteed-padded entry).
    fn new_unpadded_len_after_fold(&self, pos: usize) -> usize {
        let stride = 1usize << pos;
        let block = stride << 1;
        let l = self.current_unpadded_len;
        let current_size = 1usize << self.live_bits.len();
        if l >= current_size {
            return current_size / 2;
        }
        if l == 0 {
            return 0;
        }
        let i_min = if (l >> pos) & 1 == 0 {
            l
        } else {
            ((l >> (pos + 1)) + 1) * block
        };
        if i_min >= current_size {
            return current_size / 2;
        }
        let i_hi = i_min >> (pos + 1);
        let i_lo = i_min & (stride - 1);
        (i_hi << pos) | i_lo
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
        self.alpha_by_bit[self.current_fold_bit()]
    }

    fn compute_bare_round_poly(&mut self) -> DensePolynomial<EF> {
        if self.multilinears.is_packed() && must_unpack_multilinears::<EF>(self.multilinears.n_vars()) {
            let old = std::mem::replace(
                &mut self.multilinears,
                MleGroup::Owned(MleGroupOwned::Extension(vec![])),
            );
            self.multilinears = MleGroup::Owned(old.by_ref().unpack().as_owned_or_clone());
            self.log_packing = 0;
        }

        let pos_logical = self.current_fold_position();
        let eq_others = self.compute_eq_others();
        let alpha_fold = self.eq_alpha();
        let degree = self.computation.degree();
        let missing_mul_factor = self.missing_mul_factors.unwrap_or(EF::ONE);

        // Closed-form padding contribution: fully-padded pairs (both sides at
        // logical index >= current_unpadded_len) contribute
        // `air_at_padding * eq_others[new_j]` at every z (constant in z,
        // since the interpolation of (pad, pad) is pad). We factor it out.
        let current_size = 1usize << self.live_bits.len();
        let air_at_padding = if self.current_unpadded_len < current_size {
            padding_row_air_eval(&self.multilinears.by_ref(), &self.computation, &self.extra_data)
        } else {
            EF::ZERO
        };

        let p_evals_raw = compute_bare_at_z(
            &self.multilinears.by_ref(),
            &self.computation,
            &self.extra_data,
            &eq_others,
            self.current_unpadded_len,
            air_at_padding,
            pos_logical,
            self.log_packing,
            degree,
        );
        let mut p_evals: Vec<EF> = p_evals_raw.into_iter().map(|v| v * missing_mul_factor).collect();

        // Recover p_evals at z=1 from p(0)*(1-alpha) + p(1)*alpha = sum.
        let p_at_1 = (self.sum - (EF::ONE - alpha_fold) * p_evals[0]) / alpha_fold;
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
        let pos_logical = self.current_fold_position();
        let fold_bit = self.current_fold_bit();
        let alpha_fold = self.eq_alpha();

        let eq_eval = (EF::ONE - alpha_fold) * (EF::ONE - challenge) + alpha_fold * challenge;
        self.sum = bare_poly.evaluate(challenge) * eq_eval;

        // Rebuilding eq_others from scratch each round means no SplitEq-style
        // orphaned variable, so missing_mul_factor is just the running product
        // of per-round eq(alpha_fold, challenge).
        let prev_mmf = self.missing_mul_factors.unwrap_or(EF::ONE);
        self.missing_mul_factors = Some(eq_eval * prev_mmf);

        let pos_in_storage = pos_logical - self.log_packing;
        let folded = self.multilinears.by_ref().fold_at_bit(challenge, pos_in_storage);
        self.multilinears = MleGroup::Owned(folded);

        self.current_unpadded_len = self.new_unpadded_len_after_fold(pos_logical);
        self.live_bits.retain(|&b| b != fold_bit);
        self.current_round += 1;
    }

    fn final_column_evals(&self) -> Vec<EF> {
        match self.multilinears.by_ref() {
            MleGroupRef::Extension(cols) => cols.iter().map(|c| c[0]).collect(),
            MleGroupRef::ExtensionPacked(cols) => cols
                .iter()
                .map(|c| EFPacking::<EF>::to_ext_iter([c[0]]).next().unwrap())
                .collect(),
            MleGroupRef::Base(cols) => cols.iter().map(|c| EF::from(c[0])).collect(),
            MleGroupRef::BasePacked(cols) => cols.iter().map(|c| EF::from(c[0].as_slice()[0])).collect(),
        }
    }
}

/// Compute the bare round polynomial evaluated at z = 0, 2, 3, ..., degree.
/// Iterates pairs `(i_full_0, i_full_1)` in the current MLE's compact layout
/// that differ at `pos_logical`. `eq_others[new_j]` weights each pair, where
/// `new_j` is the index with the fold bit removed. Fully-padded pairs (both
/// sides at logical index >= `current_unpadded_len`) contribute
/// `air_at_padding * eq_others[new_j]` at every z; we factor that out and
/// add it once at the end instead of calling the AIR per pair.
fn compute_bare_at_z<'a, EF, A>(
    multilinears: &MleGroupRef<'a, EF>,
    computation: &A,
    extra_data: &A::ExtraData,
    eq_others: &[EF],
    current_unpadded_len: usize,
    air_at_padding: EF,
    pos_logical: usize,
    log_packing: usize,
    degree: usize,
) -> Vec<EF>
where
    EF: ExtensionField<PF<EF>>,
    A: Air + 'static,
    A::ExtraData: AlphaPowers<EF>,
{
    match multilinears {
        MleGroupRef::Base(cols) => compute_bare_at_z_unpacked::<EF, A, PF<EF>>(
            cols,
            computation,
            extra_data,
            eq_others,
            current_unpadded_len,
            air_at_padding,
            pos_logical,
            degree,
            <A as SumcheckComputation<EF>>::eval_base,
        ),
        MleGroupRef::Extension(cols) => compute_bare_at_z_unpacked::<EF, A, EF>(
            cols,
            computation,
            extra_data,
            eq_others,
            current_unpadded_len,
            air_at_padding,
            pos_logical,
            degree,
            <A as SumcheckComputation<EF>>::eval_extension,
        ),
        MleGroupRef::BasePacked(cols) => compute_bare_at_z_packed::<EF, A, PFPacking<EF>>(
            cols,
            computation,
            extra_data,
            eq_others,
            current_unpadded_len,
            air_at_padding,
            pos_logical,
            log_packing,
            degree,
            <A as SumcheckComputation<EF>>::eval_packed_base,
        ),
        MleGroupRef::ExtensionPacked(cols) => compute_bare_at_z_packed::<EF, A, EFPacking<EF>>(
            cols,
            computation,
            extra_data,
            eq_others,
            current_unpadded_len,
            air_at_padding,
            pos_logical,
            log_packing,
            degree,
            <A as SumcheckComputation<EF>>::eval_packed_extension,
        ),
    }
}

/// Evaluate the AIR at the padding-row values (the last logical entry of each
/// column). Only meaningful when the MLE has a constant-padded suffix; callers
/// guard on `current_unpadded_len < current_size`.
fn padding_row_air_eval<EF, A>(multilinears: &MleGroupRef<'_, EF>, computation: &A, extra_data: &A::ExtraData) -> EF
where
    EF: ExtensionField<PF<EF>>,
    A: Air + 'static,
    A::ExtraData: AlphaPowers<EF>,
{
    match multilinears {
        MleGroupRef::Base(cols) => {
            let last = cols[0].len() - 1;
            let point: Vec<PF<EF>> = cols.iter().map(|c| c[last]).collect();
            <A as SumcheckComputation<EF>>::eval_base(computation, &point, extra_data)
        }
        MleGroupRef::Extension(cols) => {
            let last = cols[0].len() - 1;
            let point: Vec<EF> = cols.iter().map(|c| c[last]).collect();
            <A as SumcheckComputation<EF>>::eval_extension(computation, &point, extra_data)
        }
        MleGroupRef::BasePacked(cols) => {
            let last_packed = cols[0].len() - 1;
            let last_lane = packing_width::<EF>() - 1;
            let point: Vec<PF<EF>> = cols.iter().map(|c| c[last_packed].as_slice()[last_lane]).collect();
            <A as SumcheckComputation<EF>>::eval_base(computation, &point, extra_data)
        }
        MleGroupRef::ExtensionPacked(cols) => {
            let last_packed = cols[0].len() - 1;
            let last_lane = packing_width::<EF>() - 1;
            let point: Vec<EF> = cols
                .iter()
                .map(|c| EFPacking::<EF>::to_ext_iter([c[last_packed]]).nth(last_lane).unwrap())
                .collect();
            <A as SumcheckComputation<EF>>::eval_extension(computation, &point, extra_data)
        }
    }
}

fn compute_bare_at_z_unpacked<EF, A, IF>(
    cols: &[&[IF]],
    computation: &A,
    extra_data: &A::ExtraData,
    eq_others: &[EF],
    current_unpadded_len: usize,
    air_at_padding: EF,
    pos_logical: usize,
    degree: usize,
    eval_fn: impl Fn(&A, &[IF], &A::ExtraData) -> EF + Sync + Send,
) -> Vec<EF>
where
    EF: ExtensionField<PF<EF>>,
    A: Air + 'static,
    A::ExtraData: AlphaPowers<EF>,
    IF: Copy + Send + Sync + std::ops::Sub<Output = IF> + std::ops::AddAssign + PrimeCharacteristicRing,
{
    let new_size = eq_others.len();
    let stride = 1usize << pos_logical;
    let lo_mask = stride - 1;
    let n_cols = cols.len();
    let (mut acc, padded_eq_sum) = (0..new_size)
        .into_par_iter()
        .with_min_len(64)
        .fold(
            || {
                (
                    EF::zero_vec(degree),
                    EF::ZERO,
                    Vec::<IF>::with_capacity(n_cols), // running column values
                    Vec::<IF>::with_capacity(n_cols), // diffs (hi - lo)
                )
            },
            |(mut acc, mut eq_sum, mut point, mut diff), new_j| {
                let i_hi = new_j >> pos_logical;
                let i_lo = new_j & lo_mask;
                let i0 = (i_hi << (pos_logical + 1)) | i_lo;
                let i1 = i0 | stride;
                let eq_val = eq_others[new_j];
                if i0 >= current_unpadded_len {
                    eq_sum += eq_val;
                    return (acc, eq_sum, point, diff);
                }
                point.clear();
                diff.clear();
                for c in cols {
                    let lo = c[i0];
                    let hi = c[i1];
                    point.push(lo);
                    diff.push(hi - lo);
                }
                // z = 0: eval at `point = lo`. Then advance once (unused, lands on z=1),
                // then eval at z = 2, 3, ..., degree inside the loop.
                acc[0] += eval_fn(computation, &point, extra_data) * eq_val;
                for k in 0..n_cols {
                    point[k] += diff[k];
                }
                for z_idx in 1..degree {
                    for k in 0..n_cols {
                        point[k] += diff[k];
                    }
                    acc[z_idx] += eval_fn(computation, &point, extra_data) * eq_val;
                }
                (acc, eq_sum, point, diff)
            },
        )
        .map(|(acc, eq_sum, _, _)| (acc, eq_sum))
        .reduce(
            || (EF::zero_vec(degree), EF::ZERO),
            |(mut a, e_a), (b, e_b)| {
                for i in 0..degree {
                    a[i] += b[i];
                }
                (a, e_a + e_b)
            },
        );
    let padding_contribution = air_at_padding * padded_eq_sum;
    for z in 0..degree {
        acc[z] += padding_contribution;
    }
    acc
}

fn compute_bare_at_z_packed<EF, A, IF>(
    cols: &[&[IF]],
    computation: &A,
    extra_data: &A::ExtraData,
    eq_others: &[EF],
    current_unpadded_len: usize,
    air_at_padding: EF,
    pos_logical: usize,
    log_packing: usize,
    degree: usize,
    eval_fn_packed: impl Fn(&A, &[IF], &A::ExtraData) -> EFPacking<EF> + Sync + Send,
) -> Vec<EF>
where
    EF: ExtensionField<PF<EF>>,
    A: Air + 'static,
    A::ExtraData: AlphaPowers<EF>,
    IF: Copy + Send + Sync + std::ops::Sub<Output = IF> + std::ops::AddAssign + PrimeCharacteristicRing,
{
    assert!(
        pos_logical >= log_packing,
        "middle-out fold bit must be above packing lanes"
    );
    let pos_packed = pos_logical - log_packing;
    let stride_packed = 1usize << pos_packed;
    let lo_mask_packed = stride_packed - 1;
    let width = 1usize << log_packing;
    let packed_new_size = eq_others.len() >> log_packing;
    assert_eq!(packed_new_size << log_packing, eq_others.len());
    // A packed entry is fully in the padded suffix iff its first logical
    // index >= current_unpadded_len, i.e. packed_i >= ceil(L / width).
    let packed_l_threshold = current_unpadded_len.div_ceil(width);

    let n_cols = cols.len();
    let (acc_packed, padded_eq_sum) = (0..packed_new_size)
        .into_par_iter()
        .with_min_len(8)
        .fold(
            || {
                (
                    vec![EFPacking::<EF>::ZERO; degree],
                    EF::ZERO,
                    Vec::<IF>::with_capacity(n_cols),
                    Vec::<IF>::with_capacity(n_cols),
                )
            },
            |(mut acc, mut eq_sum, mut point, mut diff), new_j_packed| {
                let i_hi = new_j_packed >> pos_packed;
                let i_lo = new_j_packed & lo_mask_packed;
                let i0_packed = (i_hi << (pos_packed + 1)) | i_lo;
                let i1_packed = i0_packed | stride_packed;
                let eq_slice = &eq_others[new_j_packed << log_packing..][..width];
                if i0_packed >= packed_l_threshold {
                    eq_sum += eq_slice.iter().copied().sum::<EF>();
                    return (acc, eq_sum, point, diff);
                }
                let eq_packed = EFPacking::<EF>::from_ext_slice(eq_slice);
                point.clear();
                diff.clear();
                for c in cols {
                    let lo = c[i0_packed];
                    let hi = c[i1_packed];
                    point.push(lo);
                    diff.push(hi - lo);
                }
                acc[0] += eval_fn_packed(computation, &point, extra_data) * eq_packed;
                for k in 0..n_cols {
                    point[k] += diff[k];
                }
                for z_idx in 1..degree {
                    for k in 0..n_cols {
                        point[k] += diff[k];
                    }
                    acc[z_idx] += eval_fn_packed(computation, &point, extra_data) * eq_packed;
                }
                (acc, eq_sum, point, diff)
            },
        )
        .map(|(acc, eq_sum, _, _)| (acc, eq_sum))
        .reduce(
            || (vec![EFPacking::<EF>::ZERO; degree], EF::ZERO),
            |(mut a, e_a), (b, e_b)| {
                for i in 0..degree {
                    a[i] += b[i];
                }
                (a, e_a + e_b)
            },
        );

    let padding_contribution = air_at_padding * padded_eq_sum;
    acc_packed
        .into_iter()
        .map(|p| EFPacking::<EF>::to_ext_iter([p]).sum::<EF>() + padding_contribution)
        .collect()
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
    // Per-table prefix multiplier K_t.  Grows each round during padding,
    // freezes once the table enters its active phase.
    let mut k: Vec<EF> = vec![EF::ONE; sessions.len()];
    let mut combined_coeffs = EF::zero_vec(max_full_degree + 1);
    let mut bare_polys: Vec<Option<DensePolynomial<EF>>> = vec![None; sessions.len()];

    for round in 0..n_rounds {
        combined_coeffs.fill(EF::ZERO);
        bare_polys.fill(None);

        for (idx, session) in sessions.iter_mut().enumerate() {
            let join_round = n_rounds - session.initial_n_vars();
            if round < join_round {
                // Padding
                combined_coeffs[1] += eta_powers[idx] * k[idx] * session.sum();
            } else {
                // Active: compute bare poly, expand by eq_linear, scale by frozen K_t
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
            parallel_clone(&column[1..], &mut down[..column.len() - 1]);
            down[column.len() - 1] = column[column.len() - 1];
            down
        })
        .collect()
}

pub fn columns_evals_up_and_down<EF: ExtensionField<PF<EF>>, A: Air>(
    air: &A,
    col_evals: &[EF],
    point_natural: &[EF],
) -> (MultilinearPoint<EF>, BTreeMap<ColIndex, EF>, BTreeMap<ColIndex, EF>) {
    let n_up = air.n_columns();
    debug_assert_eq!(col_evals.len(), n_up + air.n_down_columns());

    let point = MultilinearPoint(point_natural.to_vec());

    let evals_eq: BTreeMap<ColIndex, EF> = col_evals[..n_up].iter().copied().enumerate().collect();
    let evals_next: BTreeMap<ColIndex, EF> = col_evals[n_up..]
        .iter()
        .zip(air.down_column_indexes())
        .map(|(&v, col_index)| (col_index, v))
        .collect();

    (point, evals_eq, evals_next)
}

pub fn back_loaded_table_contribution<EF: ExtensionField<PF<EF>>>(
    bus_point: &[EF],
    sumcheck_air_point: &[EF],
    point_natural: &[EF],
    constraint_eval: EF,
    eta_power: EF,
) -> EF {
    let n_t = bus_point.len();
    let n_max = sumcheck_air_point.len();
    let suffix_start = n_max - n_t;
    assert_eq!(point_natural.len(), n_t);
    let eq_val = MultilinearPoint(bus_point.to_vec()).eq_poly_outside(&MultilinearPoint(point_natural.to_vec()));
    let k_t: EF = sumcheck_air_point[..suffix_start].iter().copied().product();
    eta_power * k_t * eq_val * constraint_eval
}
