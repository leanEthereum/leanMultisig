use crate::*;
use air::*;
use field::*;
use poly::*;
use rayon::prelude::*;
use std::any::TypeId;
use std::ops::{Add, AddAssign, Mul, MulAssign, Sub};

pub trait SumcheckComputation<EF: ExtensionField<PF<EF>>>: Sync {
    type ExtraData: Send + Sync + 'static;

    fn degree(&self) -> usize;
    fn eval_base(&self, point_f: &[PF<EF>], extra_data: &Self::ExtraData) -> EF;
    fn eval_extension(&self, point_f: &[EF], extra_data: &Self::ExtraData) -> EF;
    fn eval_packed_base(&self, point_f: &[PFPacking<EF>], extra_data: &Self::ExtraData) -> EFPacking<EF>;
    fn eval_packed_extension(&self, point_f: &[EFPacking<EF>], extra_data: &Self::ExtraData) -> EFPacking<EF>;
}

macro_rules! impl_air_eval {
    ($self:expr, $point_f:expr, $extra_data:expr, $folder_ty:ident) => {{
        let n_cols = $self.n_columns();
        let mut folder = $folder_ty {
            up: &$point_f[..n_cols],
            down: &$point_f[n_cols..],
            extra_data: $extra_data,
            accumulator: Default::default(),
            constraint_index: 0,
        };
        Air::eval($self, &mut folder, $extra_data);
        folder.accumulator
    }};
}

impl<EF, A> SumcheckComputation<EF> for A
where
    EF: ExtensionField<PF<EF>>,
    A: Send + Sync + Air,
    A::ExtraData: AlphaPowers<EF>,
{
    type ExtraData = A::ExtraData;

    #[inline(always)]
    fn eval_base(&self, point_f: &[PF<EF>], extra_data: &Self::ExtraData) -> EF {
        impl_air_eval!(self, point_f, extra_data, ConstraintFolder)
    }

    #[inline(always)]
    fn eval_extension(&self, point_f: &[EF], extra_data: &Self::ExtraData) -> EF {
        impl_air_eval!(self, point_f, extra_data, ConstraintFolder)
    }

    #[inline(always)]
    fn eval_packed_base(&self, point_f: &[PFPacking<EF>], extra_data: &Self::ExtraData) -> EFPacking<EF> {
        impl_air_eval!(self, point_f, extra_data, ConstraintFolderPacked)
    }

    #[inline(always)]
    fn eval_packed_extension(&self, point_f: &[EFPacking<EF>], extra_data: &Self::ExtraData) -> EFPacking<EF> {
        impl_air_eval!(self, point_f, extra_data, ConstraintFolderPacked)
    }

    fn degree(&self) -> usize {
        self.degree_air()
    }
}

fn parallel_sum<T, F>(size: usize, n: usize, compute_iteration: F) -> Vec<T>
where
    T: PrimeCharacteristicRing + Send + Sync,
    F: Fn(usize) -> Vec<T> + Sync + Send,
{
    let accumulate = |mut acc: Vec<T>, sums: Vec<T>| {
        for (j, sum) in sums.into_iter().enumerate() {
            acc[j] += sum;
        }
        acc
    };

    if size < PARALLEL_THRESHOLD {
        (0..size).fold(T::zero_vec(n), |acc, i| accumulate(acc, compute_iteration(i)))
    } else {
        (0..size)
            .into_par_iter()
            .map(compute_iteration)
            .reduce(|| T::zero_vec(n), accumulate)
    }
}

fn build_evals<EF: ExtensionField<PF<EF>>>(
    sums: impl IntoIterator<Item = EF>,
    missing_mul_factor: Option<EF>,
) -> Vec<EF> {
    sums.into_iter()
        .map(|mut sum| {
            if let Some(factor) = missing_mul_factor {
                sum *= factor;
            }
            sum
        })
        .collect()
}

#[inline(always)]
fn poly_to_evals<EF: ExtensionField<PF<EF>>>(poly: &DensePolynomial<EF>) -> Vec<EF> {
    vec![poly.coeffs[0], poly.evaluate(EF::TWO)]
}

#[inline(always)]
pub(crate) fn identity_decompose<EF: Field>(e: EF) -> Vec<EF> {
    vec![e]
}

#[inline(always)]
pub(crate) fn packing_decompose<EF: ExtensionField<PF<EF>>>(e: EFPacking<EF>) -> Vec<EF> {
    EFPacking::<EF>::to_ext_iter([e]).collect()
}

#[inline(always)]
fn packing_unpack_sum<EF: ExtensionField<PF<EF>>>(s: EFPacking<EF>) -> EF {
    EFPacking::<EF>::to_ext_iter([s]).sum::<EF>()
}

fn handle_product_computation<'a, EF: ExtensionField<PF<EF>>>(group: &MleGroupRef<'a, EF>, sum: EF) -> Vec<EF> {
    let poly = match group {
        MleGroupRef::Extension(multilinears) => {
            compute_product_sumcheck_polynomial(multilinears[0], multilinears[1], sum, identity_decompose)
        }
        MleGroupRef::ExtensionPacked(multilinears) => {
            compute_product_sumcheck_polynomial(multilinears[0], multilinears[1], sum, packing_decompose)
        }
        _ => unimplemented!(),
    };
    poly_to_evals(&poly)
}

#[allow(clippy::type_complexity)]
fn handle_product_computation_with_fold<'a, EF: ExtensionField<PF<EF>>>(
    group: &MleGroupRef<'a, EF>,
    prev_folding_factor: EF,
    sum: EF,
) -> (Vec<EF>, MleGroupOwned<EF>) {
    let (poly, folded_f) = match group {
        MleGroupRef::Extension(multilinears) => {
            let (poly, folded) = fold_and_compute_product_sumcheck_polynomial(
                multilinears[0],
                multilinears[1],
                prev_folding_factor,
                sum,
                identity_decompose,
            );
            (poly, MleGroupOwned::Extension(folded))
        }
        MleGroupRef::ExtensionPacked(multilinears) => {
            let (poly, folded) = fold_and_compute_product_sumcheck_polynomial(
                multilinears[0],
                multilinears[1],
                prev_folding_factor,
                sum,
                packing_decompose,
            );
            (poly, MleGroupOwned::ExtensionPacked(folded))
        }
        _ => unimplemented!(),
    };
    (poly_to_evals(&poly), folded_f)
}

fn handle_gkr_quotient<'a, EF: ExtensionField<PF<EF>>, ED: AlphaPowers<EF>>(
    group: &MleGroupRef<'a, EF>,
    extra_data: &ED,
    first_eq_factor: EF,
    split_eq: &SplitEq<EF>,
    missing_mul_factor: Option<EF>,
    sum: EF,
) -> Vec<EF> {
    let alpha = extra_data.alpha_powers()[1];
    let mul_factor = missing_mul_factor.unwrap_or(EF::ONE);

    let poly = match group {
        MleGroupRef::Extension(m) => {
            // Materialize eq for unpacked path (small table at this stage)
            let eq_vals: Vec<EF> = (0..m[0].len() / 2).map(|i| split_eq.get_unpacked(i)).collect();
            compute_gkr_quotient_sumcheck_polynomial(
                m[0],
                m[1],
                m[2],
                m[3],
                alpha,
                first_eq_factor,
                &eq_vals,
                mul_factor,
                sum,
                identity_decompose,
            )
        }
        MleGroupRef::ExtensionPacked(m) if split_eq.is_remainder_mode() => {
            let unpack = |s: &[EFPacking<EF>]| -> Vec<EF> { EFPacking::<EF>::to_ext_iter(s.iter().copied()).collect() };
            let (m0, m1, m2, m3) = (unpack(m[0]), unpack(m[1]), unpack(m[2]), unpack(m[3]));
            let eq_vals: Vec<EF> = (0..m0.len() / 2).map(|i| split_eq.get_unpacked(i)).collect();
            compute_gkr_quotient_sumcheck_polynomial(
                &m0,
                &m1,
                &m2,
                &m3,
                alpha,
                first_eq_factor,
                &eq_vals,
                mul_factor,
                sum,
                identity_decompose,
            )
        }
        MleGroupRef::ExtensionPacked(m) => compute_gkr_quotient_sumcheck_polynomial_split_eq(
            m[0],
            m[1],
            m[2],
            m[3],
            alpha,
            first_eq_factor,
            split_eq,
            mul_factor,
            sum,
        ),
        _ => unimplemented!(),
    };
    poly_to_evals(&poly)
}

#[allow(clippy::type_complexity)]
fn handle_gkr_quotient_with_fold<'a, EF: ExtensionField<PF<EF>>, ED: AlphaPowers<EF>>(
    group: &MleGroupRef<'a, EF>,
    prev_folding_factor: EF,
    extra_data: &ED,
    first_eq_factor: EF,
    split_eq: &SplitEq<EF>,
    missing_mul_factor: Option<EF>,
    sum: EF,
) -> (Vec<EF>, MleGroupOwned<EF>) {
    let alpha = extra_data.alpha_powers()[1];
    let mul_factor = missing_mul_factor.unwrap_or(EF::ONE);

    let (poly, folded_f) = match group {
        MleGroupRef::Extension(m) => {
            // Materialize eq for the fold+compute path (small table, already halved)
            let eq_vals: Vec<EF> = (0..m[0].len() / 4).map(|i| split_eq.get_unpacked(i)).collect();
            let (poly, folded) = fold_and_compute_gkr_quotient_sumcheck_polynomial(
                prev_folding_factor,
                m[0],
                m[1],
                m[2],
                m[3],
                alpha,
                first_eq_factor,
                &eq_vals,
                mul_factor,
                sum,
                identity_decompose,
            );
            (poly, MleGroupOwned::Extension(folded))
        }
        MleGroupRef::ExtensionPacked(m) if split_eq.is_remainder_mode() => {
            let unpack = |s: &[EFPacking<EF>]| -> Vec<EF> { EFPacking::<EF>::to_ext_iter(s.iter().copied()).collect() };
            let (m0, m1, m2, m3) = (unpack(m[0]), unpack(m[1]), unpack(m[2]), unpack(m[3]));
            let eq_vals: Vec<EF> = (0..m0.len() / 4).map(|i| split_eq.get_unpacked(i)).collect();
            let (poly, folded) = fold_and_compute_gkr_quotient_sumcheck_polynomial(
                prev_folding_factor,
                &m0,
                &m1,
                &m2,
                &m3,
                alpha,
                first_eq_factor,
                &eq_vals,
                mul_factor,
                sum,
                identity_decompose,
            );
            (poly, MleGroupOwned::Extension(folded))
        }
        MleGroupRef::ExtensionPacked(m) => {
            let r = prev_folding_factor;
            let fold_ext = |u: &[EFPacking<EF>], i: usize, half: usize, quarter: usize| {
                let left = (u[i + half] - u[i]) * r + u[i];
                let right = (u[i + half + quarter] - u[i + quarter]) * r + u[i + quarter];
                (left, right)
            };
            let (poly, folded) = fold_and_compute_gkr_quotient_split_eq(
                m[0],
                m[1],
                m[2],
                m[3],
                fold_ext,
                fold_ext,
                alpha,
                first_eq_factor,
                split_eq,
                mul_factor,
                sum,
            );
            (poly, MleGroupOwned::ExtensionPacked(folded))
        }
        _ => unimplemented!(),
    };
    (poly_to_evals(&poly), folded_f)
}

pub struct SumcheckComputeParams<'a, EF: ExtensionField<PF<EF>>, SC: SumcheckComputation<EF>> {
    pub split_eq: Option<&'a SplitEq<EF>>,
    pub first_eq_factor: Option<EF>,
    pub computation: &'a SC,
    pub extra_data: &'a SC::ExtraData,
    pub missing_mul_factor: Option<EF>,
    pub sum: EF,
}

pub fn sumcheck_compute<'a, EF: ExtensionField<PF<EF>>, SC>(
    group: &MleGroupRef<'a, EF>,
    params: SumcheckComputeParams<'a, EF, SC>,
    degree: usize,
) -> Vec<EF>
where
    SC: SumcheckComputation<EF> + 'static,
    SC::ExtraData: AlphaPowers<EF>,
{
    let SumcheckComputeParams {
        split_eq,
        first_eq_factor,
        computation,
        extra_data,
        missing_mul_factor,
        sum,
    } = params;

    let fold_size = 1 << (group.n_vars() - 1);
    let packed_fold_size = if group.is_packed() {
        fold_size / packing_width::<EF>()
    } else {
        fold_size
    };

    // Handle ProductComputation special case
    if TypeId::of::<SC>() == TypeId::of::<ProductComputation>() && split_eq.is_none() {
        assert!(missing_mul_factor.is_none());
        assert!(extra_data.alpha_powers().is_empty());
        assert_eq!(group.n_columns(), 2);
        return handle_product_computation(group, sum);
    }

    // Handle GKRQuotientComputation special case
    if TypeId::of::<SC>() == TypeId::of::<GKRQuotientComputation>() {
        assert!(split_eq.is_some());
        assert_eq!(group.n_columns(), 4);
        return handle_gkr_quotient(
            group,
            extra_data,
            first_eq_factor.unwrap(),
            split_eq.unwrap(),
            missing_mul_factor,
            sum,
        );
    }

    match group {
        MleGroupRef::ExtensionPacked(multilinears) if split_eq.is_some() => {
            assert!(!split_eq.unwrap().is_remainder_mode());
            sumcheck_compute_with_split_eq(
                multilinears,
                degree,
                split_eq.unwrap(),
                computation,
                extra_data,
                missing_mul_factor,
                packed_fold_size,
                |sc, pf, ed| sc.eval_packed_extension(&pf, ed),
                packing_unpack_sum,
            )
        }
        MleGroupRef::ExtensionPacked(multilinears) => sumcheck_compute_core(
            multilinears,
            degree,
            |i| split_eq.map(|seq| seq.get_packed(i)),
            computation,
            extra_data,
            missing_mul_factor,
            packed_fold_size,
            |sc, pf, ed| sc.eval_packed_extension(&pf, ed),
            packing_unpack_sum,
        ),
        MleGroupRef::BasePacked(multilinears) => sumcheck_compute_core(
            multilinears,
            degree,
            |i| split_eq.map(|seq| seq.get_packed(i)),
            computation,
            extra_data,
            missing_mul_factor,
            packed_fold_size,
            |sc, pf, ed| sc.eval_packed_base(&pf, ed),
            packing_unpack_sum,
        ),
        MleGroupRef::Base(multilinears) => sumcheck_compute_core(
            multilinears,
            degree,
            |i| split_eq.map(|seq| seq.get_unpacked(i)),
            computation,
            extra_data,
            missing_mul_factor,
            fold_size,
            |sc, pf, ed| sc.eval_base(&pf, ed),
            |s| s,
        ),
        MleGroupRef::Extension(multilinears) => sumcheck_compute_core(
            multilinears,
            degree,
            |i| split_eq.map(|seq| seq.get_unpacked(i)),
            computation,
            extra_data,
            missing_mul_factor,
            fold_size,
            |sc, pf, ed| sc.eval_extension(&pf, ed),
            |s| s,
        ),
    }
}

#[allow(clippy::type_complexity)]
pub fn fold_and_sumcheck_compute<'a, EF: ExtensionField<PF<EF>>, SC>(
    prev_folding_factor: EF,
    group: &MleGroupRef<'a, EF>,
    params: SumcheckComputeParams<'a, EF, SC>,
    degree: usize,
) -> (Vec<EF>, MleGroupOwned<EF>)
where
    SC: SumcheckComputation<EF> + 'static,
    SC::ExtraData: AlphaPowers<EF>,
{
    let SumcheckComputeParams {
        split_eq,
        first_eq_factor,
        computation,
        extra_data,
        missing_mul_factor,
        sum,
    } = params;

    let fold_size = 1 << (group.n_vars() - 2);
    let compute_fold_size = if group.is_packed() {
        fold_size / packing_width::<EF>()
    } else {
        fold_size
    };

    // Handle ProductComputation special case
    if TypeId::of::<SC>() == TypeId::of::<ProductComputation>() && split_eq.is_none() {
        assert!(missing_mul_factor.is_none());
        assert!(extra_data.alpha_powers().is_empty());
        assert_eq!(group.n_columns(), 2);
        return handle_product_computation_with_fold(group, prev_folding_factor, sum);
    }

    // Handle GKRQuotientComputation special case
    if TypeId::of::<SC>() == TypeId::of::<GKRQuotientComputation>() {
        assert!(split_eq.is_some());
        assert_eq!(group.n_columns(), 4);
        return handle_gkr_quotient_with_fold(
            group,
            prev_folding_factor,
            extra_data,
            first_eq_factor.unwrap(),
            split_eq.unwrap(),
            missing_mul_factor,
            sum,
        );
    }

    match group {
        MleGroupRef::ExtensionPacked(multilinears) if split_eq.is_some() => {
            assert!(!split_eq.unwrap().is_remainder_mode());
            let prev_folded_size = multilinears[0].len() / 2;
            sumcheck_fold_and_compute_with_split_eq(
                multilinears,
                degree,
                split_eq.unwrap(),
                computation,
                extra_data,
                missing_mul_factor,
                compute_fold_size,
                |m, id| (m[id + prev_folded_size] - m[id]) * prev_folding_factor + m[id],
                |sc, pf, ed| sc.eval_packed_extension(&pf, ed),
                packing_unpack_sum,
                MleGroupOwned::ExtensionPacked,
            )
        }
        MleGroupRef::ExtensionPacked(multilinears) => {
            let prev_folded_size = multilinears[0].len() / 2;
            sumcheck_fold_and_compute_core(
                multilinears,
                degree,
                |i| split_eq.map(|seq| seq.get_packed(i)),
                computation,
                extra_data,
                missing_mul_factor,
                compute_fold_size,
                |m, id| (m[id + prev_folded_size] - m[id]) * prev_folding_factor + m[id],
                |sc, pf, ed| sc.eval_packed_extension(&pf, ed),
                packing_unpack_sum,
                MleGroupOwned::ExtensionPacked,
            )
        }
        MleGroupRef::BasePacked(multilinears) => {
            let prev_folded_size = multilinears[0].len() / 2;
            let prev_folding_factor_packed = EFPacking::<EF>::from(prev_folding_factor);
            sumcheck_fold_and_compute_core(
                multilinears,
                degree,
                |i| split_eq.map(|seq| seq.get_packed(i)),
                computation,
                extra_data,
                missing_mul_factor,
                compute_fold_size,
                |m, id| prev_folding_factor_packed * (m[id + prev_folded_size] - m[id]) + m[id],
                |sc, pf, ed| sc.eval_packed_extension(&pf, ed),
                packing_unpack_sum,
                MleGroupOwned::ExtensionPacked,
            )
        }
        MleGroupRef::Base(multilinears) => {
            let prev_folded_size = multilinears[0].len() / 2;
            sumcheck_fold_and_compute_core(
                multilinears,
                degree,
                |i| split_eq.map(|seq| seq.get_unpacked(i)),
                computation,
                extra_data,
                missing_mul_factor,
                compute_fold_size,
                |m, id| prev_folding_factor * (m[id + prev_folded_size] - m[id]) + m[id],
                |sc, pf, ed| sc.eval_extension(&pf, ed),
                |s| s,
                MleGroupOwned::Extension,
            )
        }
        MleGroupRef::Extension(multilinears) => {
            let prev_folded_size = multilinears[0].len() / 2;
            sumcheck_fold_and_compute_core(
                multilinears,
                degree,
                |i| split_eq.map(|seq| seq.get_unpacked(i)),
                computation,
                extra_data,
                missing_mul_factor,
                compute_fold_size,
                |m, id| (m[id + prev_folded_size] - m[id]) * prev_folding_factor + m[id],
                |sc, pf, ed| sc.eval_extension(&pf, ed),
                |s| s,
                MleGroupOwned::Extension,
            )
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn sumcheck_compute_core<EF, IF, EFT, SC>(
    multilinears: &[&[IF]],
    degree: usize,
    eq_at: impl Fn(usize) -> Option<EFT> + Sync + Send,
    computation: &SC,
    extra_data: &SC::ExtraData,
    missing_mul_factor: Option<EF>,
    fold_size: usize,
    eval_fn: impl Fn(&SC, Vec<IF>, &SC::ExtraData) -> EFT + Sync + Send,
    unpack_sum: impl Fn(EFT) -> EF,
) -> Vec<EF>
where
    EF: ExtensionField<PF<EF>>,
    IF: Copy + Sub<Output = IF> + Add<Output = IF> + AddAssign + Send + Sync,
    EFT: PrimeCharacteristicRing
        + Copy
        + Sub<Output = EFT>
        + Add<Output = EFT>
        + Send
        + Sync
        + Mul<EFT, Output = EFT>
        + MulAssign,
    SC: SumcheckComputation<EF>,
{
    let compute_at = |i: usize, eq_val: Option<EFT>| -> Vec<EFT> {
        let mut rows = multilinears
            .iter()
            .map(|m| {
                let lo = m[i];
                let hi = m[i + fold_size];
                let diff_hi_lo = hi - lo;
                [lo, diff_hi_lo, diff_hi_lo]
            })
            .collect::<Vec<_>>();

        // z = 0
        let point_0 = rows.iter().map(|row| row[0]).collect::<Vec<_>>();
        let mut eval_0 = eval_fn(computation, point_0, extra_data);
        if let Some(eq) = eq_val {
            eval_0 *= eq;
        }

        let mut evals = Vec::with_capacity(degree);
        evals.push(eval_0);

        // z = 2, 3 ...
        for _ in 1..degree {
            for [_, diff_hi_lo, acc] in &mut rows {
                *acc += *diff_hi_lo;
            }
            let point_f = rows.iter().map(|row| row[0] + row[2]).collect::<Vec<_>>();
            let mut eval = eval_fn(computation, point_f, extra_data);
            if let Some(eq) = eq_val {
                eval *= eq;
            }
            evals.push(eval);
        }
        evals
    };

    let sums = parallel_sum(fold_size, degree, |i| compute_at(i, eq_at(i)));
    let unpacked_sums = sums.into_iter().map(&unpack_sum);
    build_evals(unpacked_sums, missing_mul_factor)
}

#[allow(clippy::too_many_arguments)]
#[allow(clippy::type_complexity)]
fn sumcheck_fold_and_compute_core<EF, IF, FT, SC>(
    multilinears: &[&[IF]],
    degree: usize,
    eq_at: impl Fn(usize) -> Option<FT> + Sync + Send,
    computation: &SC,
    extra_data: &SC::ExtraData,
    missing_mul_factor: Option<EF>,
    compute_fold_size: usize,
    fold_f: impl Fn(&[IF], usize) -> FT + Sync + Send,
    eval_fn: impl Fn(&SC, Vec<FT>, &SC::ExtraData) -> FT + Sync + Send,
    unpack_sum: impl Fn(FT) -> EF,
    wrap_f: impl FnOnce(Vec<Vec<FT>>) -> MleGroupOwned<EF>,
) -> (Vec<EF>, MleGroupOwned<EF>)
where
    EF: ExtensionField<PF<EF>>,
    IF: Copy + Send + Sync,
    FT: PrimeCharacteristicRing + Copy + Sub<Output = FT> + Add<Output = FT> + Send + Sync,
    SC: SumcheckComputation<EF>,
{
    let prev_folded_size = 2 * compute_fold_size;

    let folded_f: Vec<Vec<FT>> = (0..multilinears.len())
        .map(|_| FT::zero_vec(prev_folded_size))
        .collect();

    let compute_iteration = |i: usize| -> Vec<FT> {
        let eq_mle_eval = eq_at(i);

        let mut rows_f: Vec<[FT; 3]> = multilinears
            .iter()
            .enumerate()
            .map(|(j, m)| {
                let lo = fold_f(m, i);
                let hi = fold_f(m, i + compute_fold_size);
                unsafe {
                    let ptr = folded_f[j].as_ptr() as *mut FT;
                    *ptr.add(i) = lo;
                    *ptr.add(i + compute_fold_size) = hi;
                }
                let diff_hi_lo = hi - lo;
                [lo, diff_hi_lo, diff_hi_lo]
            })
            .collect();

        // z = 0
        let point_0 = rows_f.iter().map(|row| row[0]).collect::<Vec<FT>>();
        let mut eval_0 = eval_fn(computation, point_0, extra_data);
        if let Some(eq) = eq_mle_eval {
            eval_0 *= eq;
        }

        let mut evals = Vec::with_capacity(degree);
        evals.push(eval_0);

        // z = 2, 3 ...
        for _ in 1..degree {
            for [_, diff_hi_lo, acc] in &mut rows_f {
                *acc += *diff_hi_lo;
            }
            let point_f = rows_f.iter().map(|row| row[0] + row[2]).collect::<Vec<FT>>();
            let mut eval = eval_fn(computation, point_f, extra_data);
            if let Some(eq) = eq_mle_eval {
                eval *= eq;
            }
            evals.push(eval);
        }
        evals
    };

    let sums = parallel_sum(compute_fold_size, degree, compute_iteration);
    let unpacked_sums = sums.into_iter().map(&unpack_sum);
    (build_evals(unpacked_sums, missing_mul_factor), wrap_f(folded_f))
}

#[allow(clippy::too_many_arguments, clippy::needless_range_loop)]
fn sumcheck_compute_with_split_eq<EF, SC>(
    multilinears: &[&[EFPacking<EF>]],
    degree: usize,
    split_eq: &SplitEq<EF>,
    computation: &SC,
    extra_data: &SC::ExtraData,
    missing_mul_factor: Option<EF>,
    fold_size: usize,
    eval_fn: impl Fn(&SC, Vec<EFPacking<EF>>, &SC::ExtraData) -> EFPacking<EF> + Sync + Send,
    unpack_sum: impl Fn(EFPacking<EF>) -> EF,
) -> Vec<EF>
where
    EF: ExtensionField<PF<EF>>,
    SC: SumcheckComputation<EF>,
{
    let n_lo = split_eq.n_lo();
    let packed_hi = split_eq.packed_hi();
    let log_packed_hi = split_eq.log_packed_hi;
    let eq_lo = &split_eq.eq_lo;
    let eq_hi = &split_eq.eq_hi_packed;

    let zero = || EFPacking::<EF>::zero_vec(degree);
    let accumulate = |mut acc: Vec<EFPacking<EF>>, vals: Vec<EFPacking<EF>>| -> Vec<EFPacking<EF>> {
        for (a, v) in acc.iter_mut().zip(vals.iter()) {
            *a += *v;
        }
        acc
    };

    let sums: Vec<EFPacking<EF>> = (0..n_lo)
        .into_par_iter()
        .map(|b_lo| {
            let eq_lo_bc = EFPacking::<EF>::from(eq_lo[b_lo]);
            let base = b_lo << log_packed_hi;
            let mut block_acc = zero();
            for k in 0..packed_hi {
                let i = base + k;
                let eq_val = eq_hi[k];

                let mut rows = multilinears
                    .iter()
                    .map(|m| {
                        let lo = m[i];
                        let hi = m[i + fold_size];
                        let diff = hi - lo;
                        [lo, diff, diff]
                    })
                    .collect::<Vec<_>>();

                // z = 0
                let p0 = rows.iter().map(|r| r[0]).collect();
                let mut e0 = eval_fn(computation, p0, extra_data);
                e0 *= eq_val;
                block_acc[0] += e0;

                // z = 2, 3, ...
                for d in 1..degree {
                    for [_, diff, acc] in &mut rows {
                        *acc += *diff;
                    }
                    let pf = rows.iter().map(|r| r[0] + r[2]).collect();
                    let mut ev = eval_fn(computation, pf, extra_data);
                    ev *= eq_val;
                    block_acc[d] += ev;
                }
            }
            for a in &mut block_acc {
                *a *= eq_lo_bc;
            }
            block_acc
        })
        .reduce(zero, accumulate);

    let unpacked = sums.into_iter().map(&unpack_sum);
    build_evals(unpacked, missing_mul_factor)
}

#[allow(clippy::too_many_arguments, clippy::needless_range_loop)]
#[allow(clippy::type_complexity)]
fn sumcheck_fold_and_compute_with_split_eq<EF, IF, SC>(
    multilinears: &[&[IF]],
    degree: usize,
    split_eq: &SplitEq<EF>,
    computation: &SC,
    extra_data: &SC::ExtraData,
    missing_mul_factor: Option<EF>,
    compute_fold_size: usize,
    fold_f: impl Fn(&[IF], usize) -> EFPacking<EF> + Sync + Send,
    eval_fn: impl Fn(&SC, Vec<EFPacking<EF>>, &SC::ExtraData) -> EFPacking<EF> + Sync + Send,
    unpack_sum: impl Fn(EFPacking<EF>) -> EF,
    wrap_f: impl FnOnce(Vec<Vec<EFPacking<EF>>>) -> MleGroupOwned<EF>,
) -> (Vec<EF>, MleGroupOwned<EF>)
where
    EF: ExtensionField<PF<EF>>,
    IF: Copy + Send + Sync,
    SC: SumcheckComputation<EF>,
{
    let prev_folded_size = 2 * compute_fold_size;
    let folded_f: Vec<Vec<EFPacking<EF>>> = (0..multilinears.len())
        .map(|_| EFPacking::<EF>::zero_vec(prev_folded_size))
        .collect();

    let n_lo = split_eq.n_lo();
    let packed_hi = split_eq.packed_hi();
    let log_packed_hi = split_eq.log_packed_hi;
    let eq_lo = &split_eq.eq_lo;
    let eq_hi = &split_eq.eq_hi_packed;

    let zero = || EFPacking::<EF>::zero_vec(degree);
    let accumulate = |mut acc: Vec<EFPacking<EF>>, vals: Vec<EFPacking<EF>>| -> Vec<EFPacking<EF>> {
        for (a, v) in acc.iter_mut().zip(vals.iter()) {
            *a += *v;
        }
        acc
    };

    let sums: Vec<EFPacking<EF>> = (0..n_lo)
        .into_par_iter()
        .map(|b_lo| {
            let eq_lo_bc = EFPacking::<EF>::from(eq_lo[b_lo]);
            let base = b_lo << log_packed_hi;
            let mut block_acc = zero();
            for k in 0..packed_hi {
                let i = base + k;
                let eq_val = eq_hi[k];

                let mut rows_f: Vec<[EFPacking<EF>; 3]> = multilinears
                    .iter()
                    .enumerate()
                    .map(|(j, m)| {
                        let lo = fold_f(m, i);
                        let hi = fold_f(m, i + compute_fold_size);
                        unsafe {
                            let ptr = folded_f[j].as_ptr() as *mut EFPacking<EF>;
                            *ptr.add(i) = lo;
                            *ptr.add(i + compute_fold_size) = hi;
                        }
                        let diff = hi - lo;
                        [lo, diff, diff]
                    })
                    .collect();

                let p0 = rows_f.iter().map(|r| r[0]).collect();
                let mut e0 = eval_fn(computation, p0, extra_data);
                e0 *= eq_val;
                block_acc[0] += e0;

                for d in 1..degree {
                    for [_, diff, acc] in &mut rows_f {
                        *acc += *diff;
                    }
                    let pf = rows_f.iter().map(|r| r[0] + r[2]).collect();
                    let mut ev = eval_fn(computation, pf, extra_data);
                    ev *= eq_val;
                    block_acc[d] += ev;
                }
            }
            for a in &mut block_acc {
                *a *= eq_lo_bc;
            }
            block_acc
        })
        .reduce(zero, accumulate);

    let unpacked = sums.into_iter().map(&unpack_sum);
    (build_evals(unpacked, missing_mul_factor), wrap_f(folded_f))
}
