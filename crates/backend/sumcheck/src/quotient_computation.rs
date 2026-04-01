use std::{
    array,
    ops::{Add, Mul, MulAssign},
};

use field::{Algebra, ExtensionField, Field, PrimeCharacteristicRing};
use poly::*;
use rayon::iter::IntoParallelRefIterator;
use rayon::prelude::*;

use crate::{SplitEq, SumcheckComputation, sumcheck_quadratic};

#[derive(Default, Debug)]
pub struct GKRQuotientComputation;

impl<EF: ExtensionField<PF<EF>>> SumcheckComputation<EF> for GKRQuotientComputation {
    type ExtraData = Vec<EF>;

    fn degree(&self) -> usize {
        2
    }

    #[inline(always)]
    fn eval_base(&self, point: &[PF<EF>], alpha_powers: &Self::ExtraData) -> EF {
        let inner = sum_fractions_const_2_by_2(&point[..2], &point[2..]);
        my_dot_product(&alpha_powers[1..], &inner[1..]) + inner[0]
    }

    #[inline(always)]
    fn eval_extension(&self, point: &[EF], alpha_powers: &Self::ExtraData) -> EF {
        let inner = sum_fractions_const_2_by_2(&point[..2], &point[2..]);
        my_dot_product(&alpha_powers[1..], &inner[1..]) + inner[0]
    }

    #[inline(always)]
    fn eval_packed_base(&self, point: &[PFPacking<EF>], alpha_powers: &Self::ExtraData) -> EFPacking<EF> {
        let inner = sum_fractions_const_2_by_2(&point[..2], &point[2..]);
        let alphas_packed: [_; 2] = array::from_fn(|i| EFPacking::<EF>::from(alpha_powers[i]));
        my_dot_product(&alphas_packed[1..], &inner[1..]) + inner[0]
    }

    #[inline(always)]
    fn eval_packed_extension(&self, point: &[EFPacking<EF>], alpha_powers: &Self::ExtraData) -> EFPacking<EF> {
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

/// Compute sumcheck terms for GKR quotient.
/// Supports cross-type: numerators (u0, u1) can be type N while denominators (u2, u3, eq) are type D.
/// For the same-type case, N = D.
#[inline(always)]
#[allow(clippy::too_many_arguments)]
pub fn compute_sumcheck_terms<N, D>(
    u0_left: N,
    u0_right: N,
    u1_left: N,
    u1_right: N,
    u2_left: D,
    u2_right: D,
    u3_left: D,
    u3_right: D,
    eq_val: D,
) -> (D, D, D, D)
where
    N: PrimeCharacteristicRing + Copy,
    D: Algebra<N> + Copy + MulAssign,
{
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
pub fn finalize_polynomial<A: Algebra<EF> + Copy + Send + Sync, EF: Field>(
    c0_term_single: A,
    c2_term_single: A,
    c0_term_double: A,
    c2_term_double: A,
    alpha: EF,
    first_eq_factor: EF,
    missing_mul_factor: EF,
    sum: EF,
    decompose: impl Fn(A) -> Vec<EF>,
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

/// GKR quotient sumcheck polynomial with a flat (materialized) eq table.
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

/// GKR quotient sumcheck polynomial with on-the-fly SplitEq.
/// Generic over numerator type N: works for both same-type (N = EFPacking) and
/// mixed-type (N = PFPacking, i.e. base-field numerators).
#[allow(clippy::too_many_arguments)]
pub fn compute_gkr_quotient_sumcheck_polynomial_split_eq<N, EF>(
    u0: &[N],
    u1: &[N],
    u2: &[EFPacking<EF>],
    u3: &[EFPacking<EF>],
    alpha: EF,
    first_eq_factor: EF,
    split_eq: &SplitEq<EF>,
    missing_mul_factor: EF,
    sum: EF,
) -> DensePolynomial<EF>
where
    EF: ExtensionField<PF<EF>>,
    N: PrimeCharacteristicRing + Copy + Send + Sync,
    EFPacking<EF>: Algebra<N> + Algebra<EF>,
{
    type EP<EF> = EFPacking<EF>;

    let n = u0.len();
    let half = n / 2;

    let n_lo = split_eq.n_lo();
    let packed_hi = split_eq.packed_hi();
    let eq_lo = &split_eq.eq_lo;
    let eq_hi = &split_eq.eq_hi_packed;

    let zero = || (EP::<EF>::ZERO, EP::<EF>::ZERO, EP::<EF>::ZERO, EP::<EF>::ZERO);
    let add = |a: (EP<EF>, EP<EF>, EP<EF>, EP<EF>), b: (EP<EF>, EP<EF>, EP<EF>, EP<EF>)| {
        (a.0 + b.0, a.1 + b.1, a.2 + b.2, a.3 + b.3)
    };

    let (c0s, c2s, c0d, c2d) = (0..n_lo)
        .into_par_iter()
        .fold(zero, |mut acc, b_lo| {
            let eq_lo_bc = <EP<EF> as From<EF>>::from(eq_lo[b_lo]);
            let base = b_lo * packed_hi;
            for k in 0..packed_hi {
                let i = base + k;
                let eq = eq_lo_bc * eq_hi[k];
                let t = compute_sumcheck_terms(
                    u0[i],
                    u0[i + half],
                    u1[i],
                    u1[i + half],
                    u2[i],
                    u2[i + half],
                    u3[i],
                    u3[i + half],
                    eq,
                );
                acc.0 += t.0;
                acc.1 += t.1;
                acc.2 += t.2;
                acc.3 += t.3;
            }
            acc
        })
        .reduce(zero, add);

    finalize_polynomial(
        c0s,
        c2s,
        c0d,
        c2d,
        alpha,
        first_eq_factor,
        missing_mul_factor,
        sum,
        crate::packing_decompose::<EF>,
    )
}

/// Fold + compute GKR quotient with a flat (materialized) eq table.
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

// SAFETY: SendPtr wraps a raw pointer to make it Send+Sync for use in
// rayon parallel iterators where disjoint index ranges guarantee no data races.
struct SendPtr<T>(*mut T);
unsafe impl<T> Send for SendPtr<T> {}
unsafe impl<T> Sync for SendPtr<T> {}
impl<T> Copy for SendPtr<T> {}
impl<T> Clone for SendPtr<T> {
    fn clone(&self) -> Self {
        *self
    }
}

/// Fused fold + compute GKR quotient with on-the-fly SplitEq.
/// `fold_num` folds numerator slices (type N → EFPacking), `fold_den` folds denominator slices.
#[allow(clippy::too_many_arguments)]
pub fn fold_and_compute_gkr_quotient_split_eq<N, EF>(
    u0: &[N],
    u1: &[N],
    u2: &[EFPacking<EF>],
    u3: &[EFPacking<EF>],
    fold_num: impl Fn(&[N], usize, usize, usize) -> (EFPacking<EF>, EFPacking<EF>) + Sync,
    fold_den: impl Fn(&[EFPacking<EF>], usize, usize, usize) -> (EFPacking<EF>, EFPacking<EF>) + Sync,
    alpha: EF,
    first_eq_factor: EF,
    split_eq: &SplitEq<EF>,
    missing_mul_factor: EF,
    sum: EF,
) -> (DensePolynomial<EF>, Vec<Vec<EFPacking<EF>>>)
where
    EF: ExtensionField<PF<EF>>,
    N: Copy + Send + Sync,
    EFPacking<EF>: Algebra<N> + Algebra<EF>,
{
    type EP<EF> = EFPacking<EF>;

    let n = u0.len();
    let half = n / 2;
    let quarter = n / 4;

    let mut folded_u0 = unsafe { uninitialized_vec::<EP<EF>>(half) };
    let mut folded_u1 = unsafe { uninitialized_vec::<EP<EF>>(half) };
    let mut folded_u2 = unsafe { uninitialized_vec::<EP<EF>>(half) };
    let mut folded_u3 = unsafe { uninitialized_vec::<EP<EF>>(half) };

    let p0 = SendPtr(folded_u0.as_mut_ptr());
    let p1 = SendPtr(folded_u1.as_mut_ptr());
    let p2 = SendPtr(folded_u2.as_mut_ptr());
    let p3 = SendPtr(folded_u3.as_mut_ptr());

    let zero = || (EP::<EF>::ZERO, EP::<EF>::ZERO, EP::<EF>::ZERO, EP::<EF>::ZERO);
    let add = |a: (EP<EF>, EP<EF>, EP<EF>, EP<EF>), b: (EP<EF>, EP<EF>, EP<EF>, EP<EF>)| {
        (a.0 + b.0, a.1 + b.1, a.2 + b.2, a.3 + b.3)
    };

    let n_lo = split_eq.n_lo();
    let packed_hi = split_eq.packed_hi();
    let eq_lo = &split_eq.eq_lo;
    let eq_hi = &split_eq.eq_hi_packed;

    let fold_store = |u: &[N], p: SendPtr<EP<EF>>, i: usize| {
        let (left, right) = fold_num(u, i, half, quarter);
        unsafe {
            p.0.add(i).write(left);
            p.0.add(i + quarter).write(right);
        }
        (left, right)
    };
    let fold_store_d = |u: &[EP<EF>], p: SendPtr<EP<EF>>, i: usize| {
        let (left, right) = fold_den(u, i, half, quarter);
        unsafe {
            p.0.add(i).write(left);
            p.0.add(i + quarter).write(right);
        }
        (left, right)
    };

    let (c0s, c2s, c0d, c2d) = (0..n_lo)
        .into_par_iter()
        .fold(zero, |mut acc, b_lo| {
            let eq_lo_bc = <EP<EF> as From<EF>>::from(eq_lo[b_lo]);
            let base = b_lo * packed_hi;
            for k in 0..packed_hi {
                let i = base + k;
                let eq = eq_lo_bc * eq_hi[k];

                let (u0l, u0r) = fold_store(u0, p0, i);
                let (u1l, u1r) = fold_store(u1, p1, i);
                let (u2l, u2r) = fold_store_d(u2, p2, i);
                let (u3l, u3r) = fold_store_d(u3, p3, i);
                let t = compute_sumcheck_terms(u0l, u0r, u1l, u1r, u2l, u2r, u3l, u3r, eq);
                acc.0 += t.0;
                acc.1 += t.1;
                acc.2 += t.2;
                acc.3 += t.3;
            }
            acc
        })
        .reduce(zero, add);

    (
        finalize_polynomial(
            c0s,
            c2s,
            c0d,
            c2d,
            alpha,
            first_eq_factor,
            missing_mul_factor,
            sum,
            crate::packing_decompose::<EF>,
        ),
        vec![folded_u0, folded_u1, folded_u2, folded_u3],
    )
}
