use crate::*;
use air::*;
use field::*;
use poly::*;
use rayon::prelude::*;
use std::any::TypeId;
use std::ops::Add;
use std::ops::Mul;
use utils::log2_strict_usize;

pub trait SumcheckComputation<EF: ExtensionField<PF<EF>>>: Sync {
    type ExtraData: Send + Sync + 'static;

    fn degree(&self) -> usize;
    fn eval_base(&self, point_f: &[PF<EF>], point_ef: &[EF], extra_data: &Self::ExtraData) -> EF;
    fn eval_extension(&self, point_f: &[EF], point_ef: &[EF], extra_data: &Self::ExtraData) -> EF;
    fn eval_packed_base(
        &self,
        point_f: &[PFPacking<EF>],
        point_ef: &[EFPacking<EF>],
        extra_data: &Self::ExtraData,
    ) -> EFPacking<EF>;
    fn eval_packed_extension(
        &self,
        point_f: &[EFPacking<EF>],
        point_ef: &[EFPacking<EF>],
        extra_data: &Self::ExtraData,
    ) -> EFPacking<EF>;
}

macro_rules! impl_air_eval {
    ($self:expr, $point_f:expr, $point_ef:expr, $extra_data:expr, $folder_ty:ident) => {{
        let n_cols_f = $self.n_columns_f_air();
        let n_cols_ef = $self.n_columns_ef_air();
        let mut folder = $folder_ty {
            up_f: &$point_f[..n_cols_f],
            down_f: &$point_f[n_cols_f..],
            up_ef: &$point_ef[..n_cols_ef],
            down_ef: &$point_ef[n_cols_ef..],
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
    fn eval_base(&self, point_f: &[PF<EF>], point_ef: &[EF], extra_data: &Self::ExtraData) -> EF {
        impl_air_eval!(self, point_f, point_ef, extra_data, ConstraintFolder)
    }

    #[inline(always)]
    fn eval_extension(&self, point_f: &[EF], point_ef: &[EF], extra_data: &Self::ExtraData) -> EF {
        impl_air_eval!(self, point_f, point_ef, extra_data, ConstraintFolder)
    }

    #[inline(always)]
    fn eval_packed_base(
        &self,
        point_f: &[PFPacking<EF>],
        point_ef: &[EFPacking<EF>],
        extra_data: &Self::ExtraData,
    ) -> EFPacking<EF> {
        impl_air_eval!(self, point_f, point_ef, extra_data, ConstraintFolderPackedBase)
    }

    #[inline(always)]
    fn eval_packed_extension(
        &self,
        point_f: &[EFPacking<EF>],
        point_ef: &[EFPacking<EF>],
        extra_data: &Self::ExtraData,
    ) -> EFPacking<EF> {
        impl_air_eval!(self, point_f, point_ef, extra_data, ConstraintFolderPackedExtension)
    }

    fn degree(&self) -> usize {
        self.degree_air()
    }
}

#[inline(always)]
fn extract_rows<T: Copy>(multilinears: &[&[T]], i: usize, fold_size: usize) -> Vec<Vec<T>> {
    multilinears
        .iter()
        .map(|m| (0..2).map(|j| m[i + j * fold_size]).collect())
        .collect()
}

#[inline(always)]
fn compute_point<T, S, R>(rows: &[Vec<T>], folding_factors: &[S]) -> Vec<R>
where
    T: Copy + Mul<S, Output = R>,
    S: Copy,
    R: std::iter::Sum,
{
    rows.iter()
        .map(|row| row.iter().zip(folding_factors.iter()).map(|(x, s)| *x * *s).sum())
        .collect()
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

fn convert_folding_factors<EF: ExtensionField<PF<EF>>>(folding_factors: &[Vec<PF<EF>>]) -> Vec<Vec<PFPacking<EF>>> {
    folding_factors
        .iter()
        .map(|scalars| scalars.iter().map(|s| PFPacking::<EF>::from(*s)).collect())
        .collect()
}

fn handle_product_computation<'a, EF: ExtensionField<PF<EF>>>(
    group_f: &MleGroupRef<'a, EF>,
    sum: EF,
) -> Vec<(PF<EF>, EF)> {
    let poly = match group_f {
        MleGroupRef::Extension(multilinears) => {
            compute_product_sumcheck_polynomial(&multilinears[0], &multilinears[1], sum, |e| vec![e])
        }
        MleGroupRef::ExtensionPacked(multilinears) => {
            compute_product_sumcheck_polynomial(&multilinears[0], &multilinears[1], sum, |e| {
                EFPacking::<EF>::to_ext_iter([e]).collect()
            })
        }
        _ => unimplemented!(),
    };
    poly_to_evals(&poly)
}

fn handle_product_computation_with_fold<'a, EF: ExtensionField<PF<EF>>>(
    group_f: &MleGroupRef<'a, EF>,
    prev_folding_factor: EF,
    sum: EF,
) -> (Vec<(PF<EF>, EF)>, MleGroupOwned<EF>, MleGroupOwned<EF>) {
    let (poly, folded_f) = match group_f {
        MleGroupRef::Extension(multilinears) => {
            let (poly, folded) = fold_and_compute_product_sumcheck_polynomial(
                &multilinears[0],
                &multilinears[1],
                prev_folding_factor,
                sum,
                |e| vec![e],
            );
            (poly, MleGroupOwned::Extension(folded))
        }
        MleGroupRef::ExtensionPacked(multilinears) => {
            let (poly, folded) = fold_and_compute_product_sumcheck_polynomial(
                &multilinears[0],
                &multilinears[1],
                prev_folding_factor,
                sum,
                |e| EFPacking::<EF>::to_ext_iter([e]).collect(),
            );
            (poly, MleGroupOwned::ExtensionPacked(folded))
        }
        _ => unimplemented!(),
    };
    let folded_ef = MleGroupOwned::empty(true, folded_f.is_packed());
    (poly_to_evals(&poly), folded_f, folded_ef)
}

fn handle_gkr_quotient<'a, EF: ExtensionField<PF<EF>>, ED: AlphaPowers<EF>>(
    group_f: &MleGroupRef<'a, EF>,
    extra_data: &ED,
    first_eq_factor: EF,
    eq_mle: &MleOwned<EF>,
    missing_mul_factor: Option<EF>,
    sum: EF,
) -> Vec<(PF<EF>, EF)> {
    let alpha = extra_data.alpha_powers()[1];
    let mul_factor = missing_mul_factor.unwrap_or(EF::ONE);

    let poly = match group_f {
        MleGroupRef::Extension(m) => compute_gkr_quotient_sumcheck_polynomial(
            &m[0],
            &m[1],
            &m[2],
            &m[3],
            alpha,
            first_eq_factor,
            eq_mle.as_extension().unwrap(),
            mul_factor,
            sum,
            |e| vec![e],
        ),
        MleGroupRef::ExtensionPacked(m) => compute_gkr_quotient_sumcheck_polynomial(
            &m[0],
            &m[1],
            &m[2],
            &m[3],
            alpha,
            first_eq_factor,
            eq_mle.as_extension_packed().unwrap(),
            mul_factor,
            sum,
            |e| EFPacking::<EF>::to_ext_iter([e]).collect(),
        ),
        _ => unimplemented!(),
    };
    poly_to_evals(&poly)
}

fn handle_gkr_quotient_with_fold<'a, EF: ExtensionField<PF<EF>>, ED: AlphaPowers<EF>>(
    group_f: &MleGroupRef<'a, EF>,
    prev_folding_factor: EF,
    extra_data: &ED,
    first_eq_factor: EF,
    eq_mle: &MleOwned<EF>,
    missing_mul_factor: Option<EF>,
    sum: EF,
) -> (Vec<(PF<EF>, EF)>, MleGroupOwned<EF>, MleGroupOwned<EF>) {
    let alpha = extra_data.alpha_powers()[1];
    let mul_factor = missing_mul_factor.unwrap_or(EF::ONE);

    let (poly, folded_f) = match group_f {
        MleGroupRef::Extension(m) => {
            let (poly, folded) = fold_and_compute_gkr_quotient_sumcheck_polynomial(
                prev_folding_factor,
                &m[0],
                &m[1],
                &m[2],
                &m[3],
                alpha,
                first_eq_factor,
                eq_mle.as_extension().unwrap(),
                mul_factor,
                sum,
                |e| vec![e],
            );
            (poly, MleGroupOwned::Extension(folded))
        }
        MleGroupRef::ExtensionPacked(m) => {
            let (poly, folded) = fold_and_compute_gkr_quotient_sumcheck_polynomial(
                prev_folding_factor,
                &m[0],
                &m[1],
                &m[2],
                &m[3],
                alpha,
                first_eq_factor,
                eq_mle.as_extension_packed().unwrap(),
                mul_factor,
                sum,
                |e| EFPacking::<EF>::to_ext_iter([e]).collect(),
            );
            (poly, MleGroupOwned::ExtensionPacked(folded))
        }
        _ => unimplemented!(),
    };
    let folded_ef = MleGroupOwned::empty(true, folded_f.is_packed());
    (poly_to_evals(&poly), folded_f, folded_ef)
}

// ============================================================================
// Main Public Functions
// ============================================================================

#[derive(Debug)]
pub struct SumcheckComputeParams<'a, EF: ExtensionField<PF<EF>>, SC: SumcheckComputation<EF>> {
    pub eq_mle: Option<&'a MleOwned<EF>>,
    pub first_eq_factor: Option<EF>,
    pub folding_factors: &'a [Vec<PF<EF>>],
    pub computation: &'a SC,
    pub extra_data: &'a SC::ExtraData,
    pub missing_mul_factor: Option<EF>,
    pub sum: EF,
}

pub fn sumcheck_compute<'a, EF: ExtensionField<PF<EF>>, SC>(
    group_f: &MleGroupRef<'a, EF>,
    group_ef: &MleGroupRef<'a, EF>,
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

    let fold_size = 1 << (group_f.n_vars() - 1);
    let packed_fold_size = if group_f.is_packed() {
        fold_size / packing_width::<EF>()
    } else {
        fold_size
    };

    // Handle ProductComputation special case
    if TypeId::of::<SC>() == TypeId::of::<ProductComputation>() && eq_mle.is_none() {
        assert!(missing_mul_factor.is_none());
        assert!(extra_data.alpha_powers().is_empty());
        assert_eq!(group_f.n_columns(), 2);
        assert_eq!(group_ef.n_columns(), 0);
        return handle_product_computation(group_f, sum);
    }

    // Handle GKRQuotientComputation<2> special case
    if TypeId::of::<SC>() == TypeId::of::<GKRQuotientComputation>() {
        assert!(eq_mle.is_some());
        assert_eq!(group_f.n_columns(), 4);
        assert_eq!(group_ef.n_columns(), 0);
        return handle_gkr_quotient(
            group_f,
            extra_data,
            first_eq_factor.unwrap(),
            eq_mle.unwrap(),
            missing_mul_factor,
            sum,
        );
    }

    match group_f {
        MleGroupRef::ExtensionPacked(multilinears_f) => sumcheck_compute_packed::<EF, EFPacking<EF>, _>(
            multilinears_f,
            group_ef.as_extension_packed().unwrap(),
            zs,
            eq_mle.map(|e| e.as_extension_packed().unwrap()),
            folding_factors,
            computation,
            extra_data,
            missing_mul_factor,
            packed_fold_size,
        ),
        MleGroupRef::BasePacked(multilinears_f) => sumcheck_compute_packed::<EF, PFPacking<EF>, _>(
            multilinears_f,
            group_ef.as_extension_packed().unwrap(),
            zs,
            eq_mle.map(|e| e.as_extension_packed().unwrap()),
            folding_factors,
            computation,
            extra_data,
            missing_mul_factor,
            packed_fold_size,
        ),
        MleGroupRef::Base(multilinears_f) => sumcheck_compute_not_packed(
            multilinears_f,
            group_ef.as_extension().unwrap(),
            zs,
            eq_mle.map(|e| e.as_extension().unwrap()),
            folding_factors,
            computation,
            extra_data,
            missing_mul_factor,
            fold_size,
        ),
        MleGroupRef::Extension(multilinears_f) => sumcheck_compute_not_packed(
            multilinears_f,
            group_ef.as_extension().unwrap(),
            zs,
            eq_mle.map(|e| e.as_extension().unwrap()),
            folding_factors,
            computation,
            extra_data,
            missing_mul_factor,
            fold_size,
        ),
    }
}

pub fn fold_and_sumcheck_compute<'a, EF: ExtensionField<PF<EF>>, SC>(
    prev_folding_factors: &[EF],
    group_f: &MleGroupRef<'a, EF>,
    group_ef: &MleGroupRef<'a, EF>,
    params: SumcheckComputeParams<'a, EF, SC>,
    zs: &[usize],
) -> (Vec<(PF<EF>, EF)>, MleGroupOwned<EF>, MleGroupOwned<EF>)
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

    let fold_size = 1 << (group_f.n_vars() - 1 - log2_strict_usize(prev_folding_factors.len()));
    let compute_fold_size = if group_f.is_packed() {
        fold_size / packing_width::<EF>()
    } else {
        fold_size
    };

    let is_bi_folded = prev_folding_factors.len() == 2 && prev_folding_factors[0] == EF::ONE - prev_folding_factors[1];

    // Handle ProductComputation special case
    if TypeId::of::<SC>() == TypeId::of::<ProductComputation>() && eq_mle.is_none() {
        assert!(missing_mul_factor.is_none());
        assert!(extra_data.alpha_powers().is_empty());
        assert_eq!(group_f.n_columns(), 2);
        assert_eq!(group_ef.n_columns(), 0);
        assert!(is_bi_folded);
        return handle_product_computation_with_fold(group_f, prev_folding_factors[1], sum);
    }

    // Handle GKRQuotientComputation<2> special case
    if TypeId::of::<SC>() == TypeId::of::<GKRQuotientComputation>() {
        assert!(eq_mle.is_some());
        assert_eq!(group_f.n_columns(), 4);
        assert_eq!(group_ef.n_columns(), 0);
        assert!(is_bi_folded);
        return handle_gkr_quotient_with_fold(
            group_f,
            prev_folding_factors[1],
            extra_data,
            first_eq_factor.unwrap(),
            eq_mle.unwrap(),
            missing_mul_factor,
            sum,
        );
    }

    match group_f {
        MleGroupRef::ExtensionPacked(multilinears_f) => sumcheck_fold_and_compute_packed::<EF, EFPacking<EF>, _>(
            prev_folding_factors,
            multilinears_f,
            group_ef.as_extension_packed().unwrap(),
            zs,
            eq_mle.map(|e| e.as_extension_packed().unwrap()),
            folding_factors,
            computation,
            extra_data,
            missing_mul_factor,
            compute_fold_size,
            |wpf, ef| wpf * ef,
        ),
        MleGroupRef::BasePacked(multilinears_f) => sumcheck_fold_and_compute_packed::<EF, PFPacking<EF>, _>(
            prev_folding_factors,
            multilinears_f,
            group_ef.as_extension_packed().unwrap(),
            zs,
            eq_mle.map(|e| e.as_extension_packed().unwrap()),
            folding_factors,
            computation,
            extra_data,
            missing_mul_factor,
            compute_fold_size,
            |wpf, ef| EFPacking::<EF>::from(ef) * wpf,
        ),
        MleGroupRef::Base(multilinears_f) => sumcheck_fold_and_compute_not_packed::<EF, PF<EF>, _>(
            prev_folding_factors,
            multilinears_f,
            group_ef.as_extension().unwrap(),
            zs,
            eq_mle.map(|e| e.as_extension().unwrap()),
            folding_factors,
            computation,
            extra_data,
            missing_mul_factor,
            fold_size,
        ),
        MleGroupRef::Extension(multilinears_f) => sumcheck_fold_and_compute_not_packed::<EF, EF, _>(
            prev_folding_factors,
            multilinears_f,
            group_ef.as_extension().unwrap(),
            zs,
            eq_mle.map(|e| e.as_extension().unwrap()),
            folding_factors,
            computation,
            extra_data,
            missing_mul_factor,
            fold_size,
        ),
    }
}

// ============================================================================
// Core Computation Functions
// ============================================================================

fn sumcheck_compute_not_packed<
    EF: ExtensionField<PF<EF>> + ExtensionField<IF>,
    IF: ExtensionField<PF<EF>>,
    SC: SumcheckComputation<EF>,
>(
    multilinears_f: &[&[IF]],
    multilinears_ef: &[&[EF]],
    zs: &[usize],
    eq_mle: Option<&[EF]>,
    folding_factors: &[Vec<PF<EF>>],
    computation: &SC,
    extra_data: &SC::ExtraData,
    missing_mul_factor: Option<EF>,
    fold_size: usize,
) -> Vec<(PF<EF>, EF)> {
    let n = zs.len();

    let compute_iteration = |i: usize| -> Vec<EF> {
        let eq_mle_eval = eq_mle.map(|e| e[i]);
        let rows_f = extract_rows(multilinears_f, i, fold_size);
        let rows_ef = extract_rows(multilinears_ef, i, fold_size);

        (0..n)
            .map(|z_index| {
                let ff = &folding_factors[z_index];
                let point_f: Vec<IF> = compute_point(&rows_f, ff);
                let point_ef: Vec<EF> = compute_point(&rows_ef, ff);

                let mut res = if TypeId::of::<IF>() == TypeId::of::<PF<EF>>() {
                    let point_f = unsafe { std::mem::transmute::<Vec<IF>, Vec<PF<EF>>>(point_f) };
                    computation.eval_base(&point_f, &point_ef, extra_data)
                } else {
                    let point_f = unsafe { std::mem::transmute::<Vec<IF>, Vec<EF>>(point_f) };
                    computation.eval_extension(&point_f, &point_ef, extra_data)
                };
                if let Some(eq) = eq_mle_eval {
                    res *= eq;
                }
                res
            })
            .collect()
    };

    let sums = parallel_sum(fold_size, n, compute_iteration);
    build_evals(zs, sums, missing_mul_factor)
}

fn sumcheck_fold_and_compute_not_packed<
    EF: ExtensionField<PF<EF>> + ExtensionField<IF>,
    IF: ExtensionField<PF<EF>>,
    SC: SumcheckComputation<EF>,
>(
    prev_folding_factors: &[EF],
    multilinears_f: &[&[IF]],
    multilinears_ef: &[&[EF]],
    zs: &[usize],
    eq_mle: Option<&[EF]>,
    folding_factors: &[Vec<PF<EF>>],
    computation: &SC,
    extra_data: &SC::ExtraData,
    missing_mul_factor: Option<EF>,
    compute_fold_size: usize,
) -> (Vec<(PF<EF>, EF)>, MleGroupOwned<EF>, MleGroupOwned<EF>) {
    let bi_folded = prev_folding_factors.len() == 2 && prev_folding_factors[0] == EF::ONE - prev_folding_factors[1];
    let prev_folded_size = multilinears_f[0].len() / prev_folding_factors.len();
    let n = zs.len();

    let folded_f: Vec<Vec<EF>> = (0..multilinears_f.len())
        .map(|_| EF::zero_vec(prev_folded_size))
        .collect();
    let folded_ef: Vec<Vec<EF>> = (0..multilinears_ef.len())
        .map(|_| EF::zero_vec(prev_folded_size))
        .collect();

    let fold_value = |m: &[IF], id: usize| -> EF {
        if bi_folded {
            prev_folding_factors[1] * (m[id + prev_folded_size] - m[id]) + m[id]
        } else {
            dot_product(
                prev_folding_factors.iter().copied(),
                (0..prev_folding_factors.len()).map(|l| m[id + l * prev_folded_size]),
            )
        }
    };

    let fold_value_ef = |m: &[EF], id: usize| -> EF {
        if bi_folded {
            prev_folding_factors[1] * (m[id + prev_folded_size] - m[id]) + m[id]
        } else {
            dot_product(
                prev_folding_factors.iter().copied(),
                (0..prev_folding_factors.len()).map(|l| m[id + l * prev_folded_size]),
            )
        }
    };

    let compute_iteration = |i: usize| -> Vec<EF> {
        let eq_mle_eval = eq_mle.map(|e| e[i]);

        let rows_f: Vec<Vec<EF>> = multilinears_f
            .iter()
            .enumerate()
            .map(|(j, m)| {
                (0..2)
                    .map(|k| {
                        let id = i + k * compute_fold_size;
                        let res = fold_value(m, id);
                        unsafe {
                            let ptr = folded_f[j].as_ptr() as *mut EF;
                            *ptr.add(id) = res;
                        }
                        res
                    })
                    .collect()
            })
            .collect();

        let rows_ef: Vec<Vec<EF>> = multilinears_ef
            .iter()
            .enumerate()
            .map(|(j, m)| {
                (0..2)
                    .map(|k| {
                        let id = i + k * compute_fold_size;
                        let res = fold_value_ef(m, id);
                        unsafe {
                            let ptr = folded_ef[j].as_ptr() as *mut EF;
                            *ptr.add(id) = res;
                        }
                        res
                    })
                    .collect()
            })
            .collect();

        (0..n)
            .map(|z_index| {
                let ff = &folding_factors[z_index];
                let point_f: Vec<EF> = compute_point(&rows_f, ff);
                let point_ef: Vec<EF> = compute_point(&rows_ef, ff);

                let mut res = computation.eval_extension(&point_f, &point_ef, extra_data);
                if let Some(eq) = eq_mle_eval {
                    res *= eq;
                }
                res
            })
            .collect()
    };

    let sums = parallel_sum(compute_fold_size, n, compute_iteration);
    (
        build_evals(zs, sums, missing_mul_factor),
        MleGroupOwned::Extension(folded_f),
        MleGroupOwned::Extension(folded_ef),
    )
}

fn sumcheck_compute_packed<
    EF: ExtensionField<PF<EF>>,
    WPF: PrimeCharacteristicRing + Mul<PFPacking<EF>, Output = WPF> + Copy + Send + Sync + 'static,
    SCP: SumcheckComputation<EF>,
>(
    multilinears_f: &[&[WPF]],
    multilinears_ef: &[&[EFPacking<EF>]],
    zs: &[usize],
    eq_mle: Option<&[EFPacking<EF>]>,
    folding_factors: &[Vec<PF<EF>>],
    computation_packed: &SCP,
    extra_data: &SCP::ExtraData,
    missing_mul_factor: Option<EF>,
    packed_fold_size: usize,
) -> Vec<(PF<EF>, EF)> {
    let n = zs.len();
    let packed_ff = convert_folding_factors::<EF>(folding_factors);

    let compute_iteration = |i: usize| -> Vec<EFPacking<EF>> {
        let eq_mle_eval = eq_mle.map(|e| e[i]);
        let rows_f = extract_rows(multilinears_f, i, packed_fold_size);
        let rows_ef = extract_rows(multilinears_ef, i, packed_fold_size);

        (0..n)
            .map(|z_index| {
                let ff = &packed_ff[z_index];
                let point_f: Vec<WPF> = compute_point(&rows_f, ff);
                let point_ef: Vec<EFPacking<EF>> = compute_point(&rows_ef, ff);

                let mut res = if TypeId::of::<WPF>() == TypeId::of::<PFPacking<EF>>() {
                    let point_f = unsafe { std::mem::transmute::<Vec<WPF>, Vec<PFPacking<EF>>>(point_f) };
                    computation_packed.eval_packed_base(&point_f, &point_ef, extra_data)
                } else {
                    let point_f = unsafe { std::mem::transmute::<Vec<WPF>, Vec<EFPacking<EF>>>(point_f) };
                    computation_packed.eval_packed_extension(&point_f, &point_ef, extra_data)
                };
                if let Some(eq) = eq_mle_eval {
                    res *= eq;
                }
                res
            })
            .collect()
    };

    let sums = parallel_sum(packed_fold_size, n, compute_iteration);
    let unpacked_sums = sums.into_iter().map(|s| EFPacking::<EF>::to_ext_iter([s]).sum::<EF>());
    build_evals(zs, unpacked_sums, missing_mul_factor)
}

fn sumcheck_fold_and_compute_packed<
    EF: ExtensionField<PF<EF>>,
    WPF: PrimeCharacteristicRing + Mul<PFPacking<EF>, Output = WPF> + Copy + Send + Sync + 'static,
    SCP: SumcheckComputation<EF>,
>(
    prev_folding_factors: &[EF],
    multilinears_f: &[&[WPF]],
    multilinears_ef: &[&[EFPacking<EF>]],
    zs: &[usize],
    eq_mle: Option<&[EFPacking<EF>]>,
    folding_factors: &[Vec<PF<EF>>],
    computation_packed: &SCP,
    extra_data: &SCP::ExtraData,
    missing_mul_factor: Option<EF>,
    compute_fold_size: usize,
    mul: impl Fn(WPF, EF) -> EFPacking<EF> + Sync + Send,
) -> (Vec<(PF<EF>, EF)>, MleGroupOwned<EF>, MleGroupOwned<EF>)
where
    EFPacking<EF>: Add<WPF, Output = EFPacking<EF>>,
{
    let prev_folded_size = multilinears_f[0].len() / prev_folding_factors.len();
    let n = zs.len();
    let bi_folded = prev_folding_factors.len() == 2 && prev_folding_factors[0] == EF::ONE - prev_folding_factors[1];

    let folded_f: Vec<Vec<EFPacking<EF>>> = (0..multilinears_f.len())
        .map(|_| EFPacking::<EF>::zero_vec(prev_folded_size))
        .collect();
    let folded_ef: Vec<Vec<EFPacking<EF>>> = (0..multilinears_ef.len())
        .map(|_| EFPacking::<EF>::zero_vec(prev_folded_size))
        .collect();

    let packed_ff = convert_folding_factors::<EF>(folding_factors);

    let compute_iteration = |i: usize| -> Vec<EFPacking<EF>> {
        let eq_mle_eval = eq_mle.map(|e| e[i]);

        let rows_f: Vec<Vec<EFPacking<EF>>> = multilinears_f
            .iter()
            .enumerate()
            .map(|(j, m)| {
                (0..2)
                    .map(|k| {
                        let id = i + k * compute_fold_size;
                        let res: EFPacking<EF> = if bi_folded {
                            mul(m[id + prev_folded_size] - m[id], prev_folding_factors[1]) + m[id]
                        } else {
                            prev_folding_factors
                                .iter()
                                .enumerate()
                                .map(|(l, &f)| mul(m[id + l * prev_folded_size], f))
                                .sum()
                        };
                        unsafe {
                            let ptr = folded_f[j].as_ptr() as *mut EFPacking<EF>;
                            *ptr.add(id) = res;
                        }
                        res
                    })
                    .collect()
            })
            .collect();

        let rows_ef: Vec<Vec<EFPacking<EF>>> = multilinears_ef
            .iter()
            .enumerate()
            .map(|(j, m)| {
                (0..2)
                    .map(|k| {
                        let id = i + k * compute_fold_size;
                        let res: EFPacking<EF> = if bi_folded {
                            <EFPacking<EF> as Add>::add(
                                (m[id + prev_folded_size] - m[id]) * prev_folding_factors[1],
                                m[id],
                            )
                        } else {
                            prev_folding_factors
                                .iter()
                                .enumerate()
                                .map(|(l, &f)| m[id + l * prev_folded_size] * f)
                                .sum()
                        };
                        unsafe {
                            let ptr = folded_ef[j].as_ptr() as *mut EFPacking<EF>;
                            *ptr.add(id) = res;
                        }
                        res
                    })
                    .collect()
            })
            .collect();

        (0..n)
            .map(|z_index| {
                let ff = &packed_ff[z_index];
                let point_f: Vec<EFPacking<EF>> = compute_point(&rows_f, ff);
                let point_ef: Vec<EFPacking<EF>> = compute_point(&rows_ef, ff);

                let mut res = computation_packed.eval_packed_extension(&point_f, &point_ef, extra_data);
                if let Some(eq) = eq_mle_eval {
                    res *= eq;
                }
                res
            })
            .collect()
    };

    let sums = parallel_sum(compute_fold_size, n, compute_iteration);
    let unpacked_sums = sums.into_iter().map(|s| EFPacking::<EF>::to_ext_iter([s]).sum::<EF>());
    (
        build_evals(zs, unpacked_sums, missing_mul_factor),
        MleGroupOwned::ExtensionPacked(folded_f),
        MleGroupOwned::ExtensionPacked(folded_ef),
    )
}
