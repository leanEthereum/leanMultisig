use std::{
    array,
    ops::{Add, Mul},
};

use field::{Algebra, ExtensionField, Field};
use poly::*;
use rayon::iter::IntoParallelRefIterator;
use rayon::prelude::*;

use crate::{SumcheckComputation, sumcheck_quadratic};

#[derive(Default, Debug)]
pub struct GKRQuotientComputation;

impl<EF: ExtensionField<PF<EF>>> SumcheckComputation<EF> for GKRQuotientComputation {
    type ExtraData = Vec<EF>;

    fn degree(&self) -> usize {
        2
    }

    #[inline(always)]
    fn eval_base(&self, point: &[PF<EF>], _: &[EF], alpha_powers: &Self::ExtraData) -> EF {
        let inner = sum_fractions_const_2_by_2(&point[..2], &point[2..]);
        my_dot_product(&alpha_powers[1..], &inner[1..]) + inner[0]
    }

    #[inline(always)]
    fn eval_extension(&self, point: &[EF], _: &[EF], alpha_powers: &Self::ExtraData) -> EF {
        let inner = sum_fractions_const_2_by_2(&point[..2], &point[2..]);
        my_dot_product(&alpha_powers[1..], &inner[1..]) + inner[0]
    }

    #[inline(always)]
    fn eval_packed_base(
        &self,
        point: &[PFPacking<EF>],
        _: &[EFPacking<EF>],
        alpha_powers: &Self::ExtraData,
    ) -> EFPacking<EF> {
        let inner = sum_fractions_const_2_by_2(&point[..2], &point[2..]);
        let alphas_packed: [_; 2] = array::from_fn(|i| EFPacking::<EF>::from(alpha_powers[i]));
        my_dot_product(&alphas_packed[1..], &inner[1..]) + inner[0]
    }

    #[inline(always)]
    fn eval_packed_extension(
        &self,
        point: &[EFPacking<EF>],
        _: &[EFPacking<EF>],
        alpha_powers: &Self::ExtraData,
    ) -> EFPacking<EF> {
        let inner = sum_fractions_const_2_by_2(&point[..2], &point[2..]);
        my_dot_product(&inner[1..], &alpha_powers[1..]) + inner[0]
    }
}

#[inline(always)]
pub fn sum_fractions_const_2_by_2<A: Copy + Mul<Output = A> + Add<Output = A>>(
    numerators: &[A],
    denominators: &[A],
) -> [A; 2] {
    debug_assert_eq!(numerators.len(), 2);
    debug_assert_eq!(denominators.len(), 2);
    transmute_array([
        numerators[0] * denominators[1] + numerators[1] * denominators[0],
        denominators[0] * denominators[1],
    ])
}

#[inline(always)]
fn my_dot_product<A1: Copy + Algebra<A2>, A2: Copy>(a: &[A1], b: &[A2]) -> A1 {
    debug_assert_eq!(a.len(), b.len());
    let mut res = a[0] * b[0];
    for (x, y) in a.iter().zip(b.iter()).skip(1) {
        res += *x * *y;
    }
    res
}

#[inline(always)]
#[allow(clippy::too_many_arguments)]
fn compute_sumcheck_terms<F: Algebra<EF> + Copy + Send + Sync, EF: Field>(
    u0_left: F,
    u0_right: F,
    u1_left: F,
    u1_right: F,
    u2_left: F,
    u2_right: F,
    u3_left: F,
    u3_right: F,
    eq_val: F,
) -> (F, F, F, F) {
    let (mut c0_term_single, mut c2_term_single) = sumcheck_quadratic(((&u2_left, &u2_right), (&u3_left, &u3_right)));
    c0_term_single *= eq_val;
    c2_term_single *= eq_val;

    let (c0_term_double_a, c2_term_double_a) = sumcheck_quadratic(((&u0_left, &u0_right), (&u3_left, &u3_right)));
    let (c0_term_double_b, c2_term_double_b) = sumcheck_quadratic(((&u1_left, &u1_right), (&u2_left, &u2_right)));
    let mut c0_term_double = c0_term_double_a + c0_term_double_b;
    let mut c2_term_double = c2_term_double_a + c2_term_double_b;
    c0_term_double *= eq_val;
    c2_term_double *= eq_val;

    (c0_term_single, c2_term_single, c0_term_double, c2_term_double)
}

#[allow(clippy::too_many_arguments)]
fn finalize_polynomial<F: Algebra<EF> + Copy + Send + Sync, EF: Field>(
    c0_term_single: F,
    c2_term_single: F,
    c0_term_double: F,
    c2_term_double: F,
    alpha: EF,
    first_eq_factor: EF,
    missing_mul_factor: EF,
    sum: EF,
    decompose: impl Fn(F) -> Vec<EF>,
) -> DensePolynomial<EF> {
    let c0 = c0_term_single * alpha + c0_term_double;
    let c2 = c2_term_single * alpha + c2_term_double;

    let c0 = decompose(c0).into_iter().sum::<EF>();
    let c2 = decompose(c2).into_iter().sum::<EF>();

    let c1 = ((sum / missing_mul_factor) - c2 * first_eq_factor - c0) / first_eq_factor;

    DensePolynomial::new(vec![
        c0 * missing_mul_factor,
        c1 * missing_mul_factor,
        c2 * missing_mul_factor,
    ])
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn compute_gkr_quotient_sumcheck_polynomial<F: Algebra<EF> + Copy + Send + Sync, EF: Field>(
    u0: &[F],
    u1: &[F],
    u2: &[F],
    u3: &[F],
    alpha: EF,
    first_eq_factor: EF,
    eq_mle: &[F],
    missing_mul_factor: EF,
    sum: EF,
    decompose: impl Fn(F) -> Vec<EF>,
) -> DensePolynomial<EF> {
    let n = u0.len();
    assert_eq!(eq_mle.len(), n / 2);

    #[allow(clippy::type_complexity)]
    let map_fn = |(
        ((((u0_left, u0_right), (u1_left, u1_right)), (u2_left, u2_right)), (u3_left, u3_right)),
        &eq_val,
    ): (((((&F, &F), (&F, &F)), (&F, &F)), (&F, &F)), &F)| {
        compute_sumcheck_terms(
            *u0_left, *u0_right, *u1_left, *u1_right, *u2_left, *u2_right, *u3_left, *u3_right, eq_val,
        )
    };

    let (c0_term_single, c2_term_single, c0_term_double, c2_term_double) = if n < PARALLEL_THRESHOLD {
        iter_split_2(u0)
            .zip(iter_split_2(u1))
            .zip(iter_split_2(u2))
            .zip(iter_split_2(u3))
            .zip(eq_mle.iter())
            .map(map_fn)
            .fold(
                (F::ZERO, F::ZERO, F::ZERO, F::ZERO),
                |(a0, a1, a2, a3), (b0, b1, b2, b3)| (a0 + b0, a1 + b1, a2 + b2, a3 + b3),
            )
    } else {
        par_iter_split_2(u0)
            .zip(par_iter_split_2(u1))
            .zip(par_iter_split_2(u2))
            .zip(par_iter_split_2(u3))
            .zip(eq_mle.par_iter())
            .map(map_fn)
            .reduce(
                || (F::ZERO, F::ZERO, F::ZERO, F::ZERO),
                |(a0, a1, a2, a3), (b0, b1, b2, b3)| (a0 + b0, a1 + b1, a2 + b2, a3 + b3),
            )
    };

    finalize_polynomial(
        c0_term_single,
        c2_term_single,
        c0_term_double,
        c2_term_double,
        alpha,
        first_eq_factor,
        missing_mul_factor,
        sum,
        decompose,
    )
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn fold_and_compute_gkr_quotient_sumcheck_polynomial<F: Algebra<EF> + Copy + Send + Sync, EF: Field>(
    prev_folding_factor: EF,
    u0: &[F],
    u1: &[F],
    u2: &[F],
    u3: &[F],
    alpha: EF,
    first_eq_factor: EF,
    eq_mle: &[F],
    missing_mul_factor: EF,
    sum: EF,
    decompose: impl Fn(F) -> Vec<EF>,
) -> (DensePolynomial<EF>, Vec<Vec<F>>) {
    let n = u0.len();
    assert_eq!(eq_mle.len(), n / 4);

    let mut folded_u0 = unsafe { uninitialized_vec::<F>(n / 2) };
    let mut folded_u1 = unsafe { uninitialized_vec::<F>(n / 2) };
    let mut folded_u2 = unsafe { uninitialized_vec::<F>(n / 2) };
    let mut folded_u3 = unsafe { uninitialized_vec::<F>(n / 2) };

    let my_fold = |u: ((&F, &F), (&F, &F)), folded: (&mut F, &mut F)| {
        let u_left = *u.0.0 + (*u.1.0 - *u.0.0) * prev_folding_factor;
        let u_right = *u.0.1 + (*u.1.1 - *u.0.1) * prev_folding_factor;
        *folded.0 = u_left;
        *folded.1 = u_right;
        (u_left, u_right)
    };

    #[allow(clippy::type_complexity)]
    let map_fn = |(((((u0_prev, u0_f), (u1_prev, u1_f)), (u2_prev, u2_f)), (u3_prev, u3_f)), &eq_val): (
        (
            (
                (
                    (((&F, &F), (&F, &F)), (&mut F, &mut F)),
                    (((&F, &F), (&F, &F)), (&mut F, &mut F)),
                ),
                (((&F, &F), (&F, &F)), (&mut F, &mut F)),
            ),
            (((&F, &F), (&F, &F)), (&mut F, &mut F)),
        ),
        &F,
    )| {
        let (u0_left, u0_right) = my_fold(u0_prev, u0_f);
        let (u1_left, u1_right) = my_fold(u1_prev, u1_f);
        let (u2_left, u2_right) = my_fold(u2_prev, u2_f);
        let (u3_left, u3_right) = my_fold(u3_prev, u3_f);

        compute_sumcheck_terms(
            u0_left, u0_right, u1_left, u1_right, u2_left, u2_right, u3_left, u3_right, eq_val,
        )
    };

    let (c0_term_single, c2_term_single, c0_term_double, c2_term_double) = if n < PARALLEL_THRESHOLD {
        zip_fold_2(u0, &mut folded_u0)
            .zip(zip_fold_2(u1, &mut folded_u1))
            .zip(zip_fold_2(u2, &mut folded_u2))
            .zip(zip_fold_2(u3, &mut folded_u3))
            .zip(eq_mle.iter())
            .map(map_fn)
            .fold(
                (F::ZERO, F::ZERO, F::ZERO, F::ZERO),
                |(a0, a1, a2, a3), (b0, b1, b2, b3)| (a0 + b0, a1 + b1, a2 + b2, a3 + b3),
            )
    } else {
        par_zip_fold_2(u0, &mut folded_u0)
            .zip(par_zip_fold_2(u1, &mut folded_u1))
            .zip(par_zip_fold_2(u2, &mut folded_u2))
            .zip(par_zip_fold_2(u3, &mut folded_u3))
            .zip(eq_mle.par_iter())
            .map(map_fn)
            .reduce(
                || (F::ZERO, F::ZERO, F::ZERO, F::ZERO),
                |(a0, a1, a2, a3), (b0, b1, b2, b3)| (a0 + b0, a1 + b1, a2 + b2, a3 + b3),
            )
    };

    (
        finalize_polynomial(
            c0_term_single,
            c2_term_single,
            c0_term_double,
            c2_term_double,
            alpha,
            first_eq_factor,
            missing_mul_factor,
            sum,
            decompose,
        ),
        vec![folded_u0, folded_u1, folded_u2, folded_u3],
    )
}
