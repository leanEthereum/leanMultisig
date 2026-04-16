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

#[derive(Debug)]
pub struct AirSumcheckSession<'a, EF: ExtensionField<PF<EF>>, A: Air>
where
    A::ExtraData: AlphaPowers<EF>,
{
    multilinears: MleGroup<'a, EF>,
    eq_factor: Vec<EF>, // shrinks by 1 each round when the round's fold slot is removed.
    current_unpadded_len: usize,
    sum: EF,
    missing_mul_factor: EF,
    computation: A,
    extra_data: A::ExtraData,
    initial_n_vars: usize,
    constraints_eval_at_padding: EF,
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
        assert!(packed_multilinears.is_packed());
        let last_point = column_evals_at_logical(&packed_multilinears.by_ref(), (1usize << initial_n_vars) - 1);
        let constraints_eval_at_padding =
            <A as SumcheckComputation<EF>>::eval_extension(&computation, &last_point, &extra_data);
        Self {
            multilinears: packed_multilinears,
            eq_factor,
            current_unpadded_len: non_padded_n_rows,
            sum,
            missing_mul_factor: EF::ONE,
            computation,
            extra_data,
            initial_n_vars,
            constraints_eval_at_padding,
        }
    }

    fn current_fold_position(&self) -> usize {
        let pivot = self.initial_n_vars / 2;
        if self.eq_factor.len() > pivot {
            pivot
        } else {
            self.eq_factor.len() - 1
        }
    }

    fn current_fold_msb_index(&self) -> usize {
        self.eq_factor.len() - 1 - self.current_fold_position()
    }

    fn compute_split_eq(&self) -> SplitEq<EF> {
        let idx = self.current_fold_msb_index();
        let eq_factor_filtered: Vec<EF> = self
            .eq_factor
            .iter()
            .enumerate()
            .filter_map(|(k, &a)| (k != idx).then_some(a))
            .collect();
        SplitEq::new(&eq_factor_filtered)
    }

    fn log_packing(&self) -> usize {
        if self.multilinears.is_packed() {
            packing_log_width::<EF>()
        } else {
            0
        }
    }

    fn padding_eq_sum(&self, pos_packed: usize, t_packed: usize) -> EF {
        let n_upper = self.eq_factor.len() - self.log_packing();
        let fold_msb_idx = n_upper - 1 - pos_packed;
        let alphas_msb: Vec<EF> = (0..n_upper)
            .map(|k| if k == fold_msb_idx { EF::ZERO } else { self.eq_factor[k] })
            .collect();
        evaluate_mle_of_zero_then_ones(t_packed, &alphas_msb)
    }
}

/// nb. of integers in `[0, t)` whose bit `bit` is 0 (starting from LSB)
/// Example: t = 11, b = 1 -> Result = 6
/// 00[0]0 00[0]1 00[1]0 00[1]1 10[0]0 01[0]1 01[1]0 01[1]1 10[0]0 10[0]1 10[1]0
///  +1     +1                   +1     +1                   +1     +1
fn compute_activate_count(t: usize, bit: usize) -> usize {
    let stride: usize = 1usize << bit;
    let block = stride << 1;
    (t / block) * stride + (t % block).min(stride)
}

/// evaluate the MLE of [0, 0, ..., 0, 1, 1, ..., 1] at `alphas` where there are t zeros
fn evaluate_mle_of_zero_then_ones<EF: ExtensionField<PF<EF>>>(t: usize, alphas: &[EF]) -> EF {
    let n = alphas.len();
    if t == 0 {
        return EF::ONE;
    }
    if t >= 1usize << n {
        return EF::ZERO;
    }
    let half = 1usize << (n - 1);
    let alpha = alphas[0];
    let sub = &alphas[1..];
    if t < half {
        (EF::ONE - alpha) * evaluate_mle_of_zero_then_ones(t, sub) + alpha
    } else {
        alpha * evaluate_mle_of_zero_then_ones(t - half, sub)
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
        self.eq_factor[self.current_fold_msb_index()]
    }

    fn compute_bare_round_poly(&mut self) -> DensePolynomial<EF> {
        if self.multilinears.is_packed() && must_unpack_multilinears::<EF>(self.multilinears.n_vars()) {
            let old = std::mem::replace(
                &mut self.multilinears,
                MleGroup::Owned(MleGroupOwned::Extension(vec![])),
            );
            self.multilinears = MleGroup::Owned(old.by_ref().unpack().as_owned_or_clone());
        }

        let fold_position = self.current_fold_position();
        let split_eq = self.compute_split_eq();
        let pos_packed = fold_position - self.log_packing();

        let iter_count_no_padding = 1usize << (self.eq_factor.len() - 1 - self.log_packing());
        let current_unpadded_len_packed = self.current_unpadded_len.div_ceil(1usize << self.log_packing());
        let active_count = compute_activate_count(current_unpadded_len_packed, pos_packed);
        assert!(active_count <= iter_count_no_padding);

        let padding_contribution = if active_count < iter_count_no_padding {
            self.constraints_eval_at_padding * self.padding_eq_sum(pos_packed, current_unpadded_len_packed)
        } else {
            EF::ZERO
        };

        let p_evals_raw = compute_raw_poly(
            &self.multilinears.by_ref(),
            &self.computation,
            &self.extra_data,
            &split_eq,
            active_count,
            fold_position,
            self.log_packing(),
        );
        let mut p_evals: Vec<EF> = p_evals_raw
            .into_iter()
            .map(|v| (v + padding_contribution) * self.missing_mul_factor)
            .collect();

        // Recover p_evals at z=1 from p(0)*(1-alpha) + p(1)*alpha = sum.
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
        let pos_logical = self.current_fold_position();
        let alpha_fold = self.eq_alpha();

        let eq_eval = (EF::ONE - alpha_fold) * (EF::ONE - challenge) + alpha_fold * challenge;
        self.sum = bare_poly.evaluate(challenge) * eq_eval;
        self.missing_mul_factor *= eq_eval;

        let pos_in_storage = pos_logical - self.log_packing();
        let folded = self.multilinears.by_ref().fold_at_bit(challenge, pos_in_storage);
        self.multilinears = MleGroup::Owned(folded);

        self.current_unpadded_len = compute_activate_count(self.current_unpadded_len, pos_logical);
        self.eq_factor.remove(self.eq_factor.len() - 1 - pos_logical);
    }

    fn final_column_evals(&self) -> Vec<EF> {
        column_evals_at_logical(&self.multilinears.by_ref(), 0)
    }
}

fn column_evals_at_logical<EF: ExtensionField<PF<EF>>>(multilinears: &MleGroupRef<'_, EF>, i: usize) -> Vec<EF> {
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

#[allow(clippy::too_many_arguments)]
fn compute_raw_poly<'a, EF, A>(
    multilinears: &MleGroupRef<'a, EF>,
    computation: &A,
    extra_data: &A::ExtraData,
    split_eq: &SplitEq<EF>,
    active_count: usize,
    pos_logical: usize,
    log_packing: usize,
) -> Vec<EF>
where
    EF: ExtensionField<PF<EF>>,
    A: Air + 'static,
    A::ExtraData: AlphaPowers<EF>,
{
    let identity = |e: EF| e;
    let unpack = |p: EFPacking<EF>| EFPacking::<EF>::to_ext_iter([p]).sum::<EF>();
    let fetch_split_eq_unpacked = |s: &SplitEq<EF>, j: usize| s.get_unpacked(j);
    let fetch_split_eq_packed = |s: &SplitEq<EF>, j: usize| s.get_packed(j);

    match multilinears {
        MleGroupRef::Base(cols) => compute_raw_poly_impl::<EF, A, PF<EF>, EF>(
            cols,
            computation,
            extra_data,
            split_eq,
            active_count,
            pos_logical,
            log_packing,
            <A as SumcheckComputation<EF>>::eval_base,
            fetch_split_eq_unpacked,
            identity,
        ),
        MleGroupRef::Extension(cols) => compute_raw_poly_impl::<EF, A, EF, EF>(
            cols,
            computation,
            extra_data,
            split_eq,
            active_count,
            pos_logical,
            log_packing,
            <A as SumcheckComputation<EF>>::eval_extension,
            fetch_split_eq_unpacked,
            identity,
        ),
        MleGroupRef::BasePacked(cols) => compute_raw_poly_impl::<EF, A, PFPacking<EF>, EFPacking<EF>>(
            cols,
            computation,
            extra_data,
            split_eq,
            active_count,
            pos_logical,
            log_packing,
            <A as SumcheckComputation<EF>>::eval_packed_base,
            fetch_split_eq_packed,
            unpack,
        ),
        MleGroupRef::ExtensionPacked(cols) => compute_raw_poly_impl::<EF, A, EFPacking<EF>, EFPacking<EF>>(
            cols,
            computation,
            extra_data,
            split_eq,
            active_count,
            pos_logical,
            log_packing,
            <A as SumcheckComputation<EF>>::eval_packed_extension,
            fetch_split_eq_packed,
            unpack,
        ),
    }
}

#[allow(clippy::too_many_arguments)]
fn compute_raw_poly_impl<EF, A, IF, OF>(
    cols: &[&[IF]],
    computation: &A,
    extra_data: &A::ExtraData,
    split_eq: &SplitEq<EF>,
    active_count: usize,
    pos_logical: usize,
    log_packing: usize,
    eval_fn: impl Fn(&A, &[IF], &A::ExtraData) -> OF + Sync + Send,
    fetch_split_eq: impl Fn(&SplitEq<EF>, usize) -> OF + Sync + Send,
    finalize: impl Fn(OF) -> EF,
) -> Vec<EF>
where
    EF: ExtensionField<PF<EF>>,
    A: Air + 'static,
    A::ExtraData: AlphaPowers<EF>,
    IF: Copy + Send + Sync + std::ops::Sub<Output = IF> + std::ops::AddAssign + PrimeCharacteristicRing,
    OF: PrimeCharacteristicRing + Send + Sync,
{
    assert!(pos_logical >= log_packing,);
    let degree = computation.degree();
    let pos_packed = pos_logical - log_packing;
    let stride_packed = 1usize << pos_packed;
    let lo_mask_packed = stride_packed - 1;
    let n_cols = cols.len();

    let acc = (0..active_count)
        .into_par_iter()
        .fold(
            || {
                (
                    vec![OF::ZERO; degree],           // evals at z=0, 2, 3, ..., degree (z=1 is recovered)
                    Vec::<IF>::with_capacity(n_cols), // running column values
                    Vec::<IF>::with_capacity(n_cols), // diffs (hi - lo)
                )
            },
            |(mut acc, mut point, mut diff), new_j| {
                let i_hi = new_j >> pos_packed;
                let i_lo = new_j & lo_mask_packed;
                let i0 = (i_hi << (pos_packed + 1)) | i_lo;
                let i1 = i0 | stride_packed;
                let eq = fetch_split_eq(split_eq, new_j);
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
                acc[0] += eval_fn(computation, &point, extra_data) * eq;
                for k in 0..n_cols {
                    point[k] += diff[k];
                }
                for acc_z in &mut acc[1..] {
                    for k in 0..n_cols {
                        point[k] += diff[k];
                    }
                    *acc_z += eval_fn(computation, &point, extra_data) * eq;
                }
                (acc, point, diff)
            },
        )
        .map(|(acc, _, _)| acc)
        .reduce(
            || vec![OF::ZERO; degree],
            |mut a, b| {
                for i in 0..degree {
                    a[i] += b[i];
                }
                a
            },
        );

    acc.into_iter().map(finalize).collect()
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
            parallel_clone(&column[1..], &mut down[..column.len() - 1]);
            down[column.len() - 1] = column[column.len() - 1];
            down
        })
        .collect()
}

/// Maps the middle-out fold challenges back to natural MSB-first ordering.
/// Net effect: take the suffix of length `log_n_rows` and reverse its upper half.
pub fn natural_ordering_point_for_session<EF: Copy>(sumcheck_air_point: &[EF], log_n_rows: usize) -> Vec<EF> {
    let start = sumcheck_air_point.len() - log_n_rows;
    let half = log_n_rows.div_ceil(2);
    let mut out = sumcheck_air_point[start..start + log_n_rows].to_vec();
    out[..half].reverse();
    out
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
