use crate::*;
use air::*;
use field::*;
use poly::*;
use rayon::prelude::*;
use std::any::TypeId;
use std::ops::{Add, Mul, Sub};

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
        impl_air_eval!(self, point_f, extra_data, ConstraintFolderPackedBase)
    }

    #[inline(always)]
    fn eval_packed_extension(&self, point_f: &[EFPacking<EF>], extra_data: &Self::ExtraData) -> EFPacking<EF> {
        impl_air_eval!(self, point_f, extra_data, ConstraintFolderPackedExtension)
    }

    fn degree(&self) -> usize {
        self.degree_air()
    }
}

#[inline(always)]
fn extract_rows<T: Copy>(multilinears: &[&[T]], i: usize, fold_size: usize) -> Vec<[T; 2]> {
    multilinears.iter().map(|m| [m[i], m[i + fold_size]]).collect()
}

#[inline(always)]
fn compute_point<T, S>(rows: &[[T; 2]], z: S) -> Vec<T>
where
    T: Copy + Sub<Output = T> + Add<Output = T> + Mul<S, Output = T>,
    S: Copy,
{
    rows.iter().map(|row| (row[1] - row[0]) * z + row[0]).collect()
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
    zs: &[usize],
    sums: impl IntoIterator<Item = EF>,
    missing_mul_factor: Option<EF>,
) -> Vec<(PF<EF>, EF)> {
    zs.iter()
        .zip(sums)
        .map(|(z, mut sum)| {
            if let Some(factor) = missing_mul_factor {
                sum *= factor;
            }
            (PF::<EF>::from_usize(*z), sum)
        })
        .collect()
}

#[inline(always)]
fn poly_to_evals<EF: ExtensionField<PF<EF>>>(poly: &DensePolynomial<EF>) -> Vec<(PF<EF>, EF)> {
    vec![
        (PF::<EF>::ZERO, poly.coeffs[0]),
        (PF::<EF>::TWO, poly.evaluate(EF::TWO)),
    ]
}

fn pack_base_folding_factors<EF: ExtensionField<PF<EF>>>(folding_factors: &[PF<EF>]) -> Vec<PFPacking<EF>> {
    folding_factors.iter().map(|s| PFPacking::<EF>::from(*s)).collect()
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

fn handle_product_computation<'a, EF: ExtensionField<PF<EF>>>(
    group: &MleGroupRef<'a, EF>,
    sum: EF,
) -> Vec<(PF<EF>, EF)> {
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
) -> (Vec<(PF<EF>, EF)>, MleGroupOwned<EF>) {
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
    eq_mle: &MleOwned<EF>,
    missing_mul_factor: Option<EF>,
    sum: EF,
) -> Vec<(PF<EF>, EF)> {
    let alpha = extra_data.alpha_powers()[1];
    let mul_factor = missing_mul_factor.unwrap_or(EF::ONE);

    let poly = match group {
        MleGroupRef::Extension(m) => compute_gkr_quotient_sumcheck_polynomial(
            m[0],
            m[1],
            m[2],
            m[3],
            alpha,
            first_eq_factor,
            eq_mle.as_extension().unwrap(),
            mul_factor,
            sum,
            identity_decompose,
        ),
        MleGroupRef::ExtensionPacked(m) => compute_gkr_quotient_sumcheck_polynomial(
            m[0],
            m[1],
            m[2],
            m[3],
            alpha,
            first_eq_factor,
            eq_mle.as_extension_packed().unwrap(),
            mul_factor,
            sum,
            packing_decompose,
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
    eq_mle: &MleOwned<EF>,
    missing_mul_factor: Option<EF>,
    sum: EF,
) -> (Vec<(PF<EF>, EF)>, MleGroupOwned<EF>) {
    let alpha = extra_data.alpha_powers()[1];
    let mul_factor = missing_mul_factor.unwrap_or(EF::ONE);

    let (poly, folded_f) = match group {
        MleGroupRef::Extension(m) => {
            let (poly, folded) = fold_and_compute_gkr_quotient_sumcheck_polynomial(
                prev_folding_factor,
                m[0],
                m[1],
                m[2],
                m[3],
                alpha,
                first_eq_factor,
                eq_mle.as_extension().unwrap(),
                mul_factor,
                sum,
                identity_decompose,
            );
            (poly, MleGroupOwned::Extension(folded))
        }
        MleGroupRef::ExtensionPacked(m) => {
            let (poly, folded) = fold_and_compute_gkr_quotient_sumcheck_polynomial(
                prev_folding_factor,
                m[0],
                m[1],
                m[2],
                m[3],
                alpha,
                first_eq_factor,
                eq_mle.as_extension_packed().unwrap(),
                mul_factor,
                sum,
                packing_decompose,
            );
            (poly, MleGroupOwned::ExtensionPacked(folded))
        }
        _ => unimplemented!(),
    };
    (poly_to_evals(&poly), folded_f)
}

#[derive(Debug)]
pub struct SumcheckComputeParams<'a, EF: ExtensionField<PF<EF>>, SC: SumcheckComputation<EF>> {
    pub eq_mle: Option<&'a MleOwned<EF>>,
    pub first_eq_factor: Option<EF>,
    pub folding_factors: &'a [PF<EF>],
    pub computation: &'a SC,
    pub extra_data: &'a SC::ExtraData,
    pub missing_mul_factor: Option<EF>,
    pub sum: EF,
}

pub fn sumcheck_compute<'a, EF: ExtensionField<PF<EF>>, SC>(
    group: &MleGroupRef<'a, EF>,
    params: SumcheckComputeParams<'a, EF, SC>,
    zs: &[usize],
) -> Vec<(PF<EF>, EF)>
where
    SC: SumcheckComputation<EF> + 'static,
    SC::ExtraData: AlphaPowers<EF>,
{
    let SumcheckComputeParams {
        eq_mle,
        first_eq_factor,
        folding_factors,
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
    if TypeId::of::<SC>() == TypeId::of::<ProductComputation>() && eq_mle.is_none() {
        assert!(missing_mul_factor.is_none());
        assert!(extra_data.alpha_powers().is_empty());
        assert_eq!(group.n_columns(), 2);
        return handle_product_computation(group, sum);
    }

    // Handle GKRQuotientComputation special case
    if TypeId::of::<SC>() == TypeId::of::<GKRQuotientComputation>() {
        assert!(eq_mle.is_some());
        assert_eq!(group.n_columns(), 4);
        return handle_gkr_quotient(
            group,
            extra_data,
            first_eq_factor.unwrap(),
            eq_mle.unwrap(),
            missing_mul_factor,
            sum,
        );
    }

    match group {
        MleGroupRef::ExtensionPacked(multilinears) => {
            let packed_ff = pack_base_folding_factors::<EF>(folding_factors);
            sumcheck_compute_core(
                multilinears,
                zs,
                eq_mle.map(|e| e.as_extension_packed().unwrap()),
                &packed_ff,
                computation,
                extra_data,
                missing_mul_factor,
                packed_fold_size,
                |sc, pf, ed| sc.eval_packed_extension(&pf, ed),
                packing_unpack_sum,
            )
        }
        MleGroupRef::BasePacked(multilinears) => {
            let packed_ff = pack_base_folding_factors::<EF>(folding_factors);
            sumcheck_compute_core(
                multilinears,
                zs,
                eq_mle.map(|e| e.as_extension_packed().unwrap()),
                &packed_ff,
                computation,
                extra_data,
                missing_mul_factor,
                packed_fold_size,
                |sc, pf, ed| sc.eval_packed_base(&pf, ed),
                packing_unpack_sum,
            )
        }
        MleGroupRef::Base(multilinears) => sumcheck_compute_core(
            multilinears,
            zs,
            eq_mle.map(|e| e.as_extension().unwrap()),
            folding_factors,
            computation,
            extra_data,
            missing_mul_factor,
            fold_size,
            |sc, pf, ed| sc.eval_base(&pf, ed),
            |s| s,
        ),
        MleGroupRef::Extension(multilinears) => sumcheck_compute_core(
            multilinears,
            zs,
            eq_mle.map(|e| e.as_extension().unwrap()),
            folding_factors,
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
    zs: &[usize],
) -> (Vec<(PF<EF>, EF)>, MleGroupOwned<EF>)
where
    SC: SumcheckComputation<EF> + 'static,
    SC::ExtraData: AlphaPowers<EF>,
{
    let SumcheckComputeParams {
        eq_mle,
        first_eq_factor,
        folding_factors,
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
    if TypeId::of::<SC>() == TypeId::of::<ProductComputation>() && eq_mle.is_none() {
        assert!(missing_mul_factor.is_none());
        assert!(extra_data.alpha_powers().is_empty());
        assert_eq!(group.n_columns(), 2);
        return handle_product_computation_with_fold(group, prev_folding_factor, sum);
    }

    // Handle GKRQuotientComputation special case
    if TypeId::of::<SC>() == TypeId::of::<GKRQuotientComputation>() {
        assert!(eq_mle.is_some());
        assert_eq!(group.n_columns(), 4);
        return handle_gkr_quotient_with_fold(
            group,
            prev_folding_factor,
            extra_data,
            first_eq_factor.unwrap(),
            eq_mle.unwrap(),
            missing_mul_factor,
            sum,
        );
    }

    match group {
        MleGroupRef::ExtensionPacked(multilinears) => {
            let packed_ff = pack_base_folding_factors::<EF>(folding_factors);
            let prev_folded_size = multilinears[0].len() / 2;
            sumcheck_fold_and_compute_core(
                multilinears,
                zs,
                eq_mle.map(|e| e.as_extension_packed().unwrap()),
                &packed_ff,
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
            let packed_ff = pack_base_folding_factors::<EF>(folding_factors);
            let prev_folded_size = multilinears[0].len() / 2;
            let prev_folding_factor_packed = EFPacking::<EF>::from(prev_folding_factor);
            sumcheck_fold_and_compute_core(
                multilinears,
                zs,
                eq_mle.map(|e| e.as_extension_packed().unwrap()),
                &packed_ff,
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
                zs,
                eq_mle.map(|e| e.as_extension().unwrap()),
                folding_factors,
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
                zs,
                eq_mle.map(|e| e.as_extension().unwrap()),
                folding_factors,
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
fn sumcheck_compute_core<EF, IF, EFT, FFT, SC>(
    multilinears: &[&[IF]],
    zs: &[usize],
    eq_mle: Option<&[EFT]>,
    folding_factors: &[FFT],
    computation: &SC,
    extra_data: &SC::ExtraData,
    missing_mul_factor: Option<EF>,
    fold_size: usize,
    eval_fn: impl Fn(&SC, Vec<IF>, &SC::ExtraData) -> EFT + Sync + Send,
    unpack_sum: impl Fn(EFT) -> EF,
) -> Vec<(PF<EF>, EF)>
where
    EF: ExtensionField<PF<EF>>,
    IF: Copy + Sub<Output = IF> + Add<Output = IF> + Send + Sync + Mul<FFT, Output = IF>,
    EFT: PrimeCharacteristicRing + Copy + Sub<Output = EFT> + Add<Output = EFT> + Send + Sync + Mul<FFT, Output = EFT>,
    FFT: Copy + Send + Sync,
    SC: SumcheckComputation<EF>,
{
    let n = zs.len();

    let compute_iteration = |i: usize| -> Vec<EFT> {
        let eq_mle_eval = eq_mle.map(|e| e[i]);
        let rows = extract_rows(multilinears, i, fold_size);

        (0..n)
            .map(|z_index| {
                let ff = folding_factors[z_index];
                let point_f: Vec<IF> = compute_point(&rows, ff);

                let mut res = eval_fn(computation, point_f, extra_data);
                if let Some(eq) = eq_mle_eval {
                    res *= eq;
                }
                res
            })
            .collect()
    };

    let sums = parallel_sum(fold_size, n, compute_iteration);
    let unpacked_sums = sums.into_iter().map(&unpack_sum);
    build_evals(zs, unpacked_sums, missing_mul_factor)
}

#[allow(clippy::too_many_arguments)]
#[allow(clippy::type_complexity)]
fn sumcheck_fold_and_compute_core<EF, IF, FT, FFT, SC>(
    multilinears: &[&[IF]],
    zs: &[usize],
    eq_mle: Option<&[FT]>,
    folding_factors: &[FFT],
    computation: &SC,
    extra_data: &SC::ExtraData,
    missing_mul_factor: Option<EF>,
    compute_fold_size: usize,
    fold_f: impl Fn(&[IF], usize) -> FT + Sync + Send,
    eval_fn: impl Fn(&SC, Vec<FT>, &SC::ExtraData) -> FT + Sync + Send,
    unpack_sum: impl Fn(FT) -> EF,
    wrap_f: impl FnOnce(Vec<Vec<FT>>) -> MleGroupOwned<EF>,
) -> (Vec<(PF<EF>, EF)>, MleGroupOwned<EF>)
where
    EF: ExtensionField<PF<EF>>,
    IF: Copy + Send + Sync,
    FT: PrimeCharacteristicRing + Copy + Sub<Output = FT> + Add<Output = FT> + Send + Sync + Mul<FFT, Output = FT>,
    FFT: Copy + Send + Sync,
    SC: SumcheckComputation<EF>,
{
    let prev_folded_size = 2 * compute_fold_size;
    let n = zs.len();

    let folded_f: Vec<Vec<FT>> = (0..multilinears.len())
        .map(|_| FT::zero_vec(prev_folded_size))
        .collect();

    let compute_iteration = |i: usize| -> Vec<FT> {
        let eq_mle_eval = eq_mle.map(|e| e[i]);

        let rows_f: Vec<[FT; 2]> = multilinears
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
                [lo, hi]
            })
            .collect();

        (0..n)
            .map(|z_index| {
                let ff = folding_factors[z_index];
                let point_f: Vec<FT> = compute_point(&rows_f, ff);

                let mut res = eval_fn(computation, point_f, extra_data);
                if let Some(eq) = eq_mle_eval {
                    res *= eq;
                }
                res
            })
            .collect()
    };

    let sums = parallel_sum(compute_fold_size, n, compute_iteration);
    let unpacked_sums = sums.into_iter().map(&unpack_sum);
    (build_evals(zs, unpacked_sums, missing_mul_factor), wrap_f(folded_f))
}
