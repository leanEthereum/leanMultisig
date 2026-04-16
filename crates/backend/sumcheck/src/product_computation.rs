use fiat_shamir::*;
use field::*;
use poly::*;
use rayon::prelude::*;
use tracing::instrument;

use crate::{SumcheckComputation, sumcheck_prove_many_rounds};

#[derive(Debug)]
pub struct ProductComputation;

impl<EF: ExtensionField<PF<EF>>> SumcheckComputation<EF> for ProductComputation {
    type ExtraData = Vec<EF>;

    fn degree(&self) -> usize {
        2
    }
    #[inline(always)]
    fn eval_base(&self, _point: &[PF<EF>], _: &Self::ExtraData) -> EF {
        unreachable!()
    }
    #[inline(always)]
    fn eval_extension(&self, point: &[EF], _: &Self::ExtraData) -> EF {
        point[0] * point[1]
    }
    #[inline(always)]
    fn eval_packed_base(&self, point: &[PFPacking<EF>], _: &Self::ExtraData) -> EFPacking<EF> {
        EFPacking::<EF>::from(point[0] * point[1])
    }
    #[inline(always)]
    fn eval_packed_extension(&self, point: &[EFPacking<EF>], _: &Self::ExtraData) -> EFPacking<EF> {
        point[0] * point[1]
    }
}

#[instrument(skip_all)]
pub fn run_product_sumcheck<EF: ExtensionField<PF<EF>>>(
    pol_a: &MleRef<'_, EF>, // evals
    pol_b: &MleRef<'_, EF>, // weights
    prover_state: &mut impl FSProver<EF>,
    mut sum: EF,
    n_rounds: usize,
    pow_bits: usize,
) -> (MultilinearPoint<EF>, EF, MleOwned<EF>, MleOwned<EF>) {
    assert!(n_rounds >= 1);
    let first_sumcheck_poly = match (pol_a, pol_b) {
        (MleRef::BasePacked(evals), MleRef::ExtensionPacked(weights)) => {
            if EF::DIMENSION == 5 {
                compute_product_sumcheck_polynomial_base_ext_packed::<5, _, _, _, EF>(evals, weights, sum)
            } else {
                unimplemented!()
            }
        }
        (MleRef::ExtensionPacked(evals), MleRef::ExtensionPacked(weights)) => {
            compute_product_sumcheck_polynomial(evals, weights, sum, |e| EFPacking::<EF>::to_ext_iter([e]).collect())
        }
        (MleRef::Base(evals), MleRef::Extension(weights)) => {
            compute_product_sumcheck_polynomial(evals, weights, sum, |e| vec![e])
        }
        (MleRef::Extension(evals), MleRef::Extension(weights)) => {
            compute_product_sumcheck_polynomial(evals, weights, sum, |e| vec![e])
        }
        _ => unimplemented!(),
    };

    prover_state.add_sumcheck_polynomial(&first_sumcheck_poly.coeffs, None);
    prover_state.pow_grinding(pow_bits);
    let r1: EF = prover_state.sample();
    sum = first_sumcheck_poly.evaluate(r1);

    if n_rounds == 1 {
        return (MultilinearPoint(vec![r1]), sum, pol_a.fold(r1), pol_b.fold(r1));
    }

    let (second_sumcheck_poly, folded) = match (pol_a, pol_b) {
        (MleRef::BasePacked(evals), MleRef::ExtensionPacked(weights)) => {
            let (second_sumcheck_poly, folded) =
                fold_and_compute_product_sumcheck_polynomial(evals, weights, r1, sum, |e| {
                    EFPacking::<EF>::to_ext_iter([e]).collect()
                });
            (second_sumcheck_poly, MleGroupOwned::ExtensionPacked(folded))
        }
        (MleRef::ExtensionPacked(evals), MleRef::ExtensionPacked(weights)) => {
            let (second_sumcheck_poly, folded) =
                fold_and_compute_product_sumcheck_polynomial(evals, weights, r1, sum, |e| {
                    EFPacking::<EF>::to_ext_iter([e]).collect()
                });
            (second_sumcheck_poly, MleGroupOwned::ExtensionPacked(folded))
        }
        (MleRef::Base(evals), MleRef::Extension(weights)) => {
            let (second_sumcheck_poly, folded) =
                fold_and_compute_product_sumcheck_polynomial(evals, weights, r1, sum, |e| vec![e]);
            (second_sumcheck_poly, MleGroupOwned::Extension(folded))
        }
        (MleRef::Extension(evals), MleRef::Extension(weights)) => {
            let (second_sumcheck_poly, folded) =
                fold_and_compute_product_sumcheck_polynomial(evals, weights, r1, sum, |e| vec![e]);
            (second_sumcheck_poly, MleGroupOwned::Extension(folded))
        }
        _ => unimplemented!(),
    };

    prover_state.add_sumcheck_polynomial(&second_sumcheck_poly.coeffs, None);
    prover_state.pow_grinding(pow_bits);
    let r2: EF = prover_state.sample();
    sum = second_sumcheck_poly.evaluate(r2);

    let (mut challenges, folds, sum) = sumcheck_prove_many_rounds(
        folded,
        Some(r2),
        &ProductComputation {},
        &vec![],
        None,
        prover_state,
        sum,
        None,
        n_rounds - 2,
        false,
        pow_bits,
    );

    challenges.splice(0..0, [r1, r2]);
    let [pol_a, pol_b] = folds.split().try_into().unwrap();
    (challenges, sum, pol_a, pol_b)
}

pub fn compute_product_sumcheck_polynomial<
    F: PrimeCharacteristicRing + Copy + Send + Sync,
    EF: Field,
    EFPacking: Algebra<F> + Copy + Send + Sync,
>(
    pol_0: &[F],         // evals
    pol_1: &[EFPacking], // weights
    sum: EF,
    decompose: impl Fn(EFPacking) -> Vec<EF>,
) -> DensePolynomial<EF> {
    let n = pol_0.len();
    assert_eq!(n, pol_1.len());
    assert!(n.is_power_of_two());

    let num_elements = n;

    let (c0_packed, c2_packed) = if num_elements < PARALLEL_THRESHOLD {
        pol_0[..n / 2]
            .iter()
            .zip(pol_0[n / 2..].iter())
            .zip(pol_1[..n / 2].iter().zip(pol_1[n / 2..].iter()))
            .map(sumcheck_quadratic)
            .fold((EFPacking::ZERO, EFPacking::ZERO), |(a0, a2), (b0, b2)| {
                (a0 + b0, a2 + b2)
            })
    } else {
        pol_0[..n / 2]
            .par_iter()
            .zip(pol_0[n / 2..].par_iter())
            .zip(pol_1[..n / 2].par_iter().zip(pol_1[n / 2..].par_iter()))
            .map(sumcheck_quadratic)
            .reduce(
                || (EFPacking::ZERO, EFPacking::ZERO),
                |(a0, a2), (b0, b2)| (a0 + b0, a2 + b2),
            )
    };

    let c0 = decompose(c0_packed).into_iter().sum::<EF>();
    let c2 = decompose(c2_packed).into_iter().sum::<EF>();
    let c1 = sum - c0.double() - c2;

    DensePolynomial::new(vec![c0, c1, c2])
}

// using delayed modular reduction
pub fn compute_product_sumcheck_polynomial_base_ext_packed<
    const DIM: usize,
    F: PrimeField32,
    PF: PackedField<Scalar = F>,
    EFP: BasedVectorSpace<PF> + Copy + Send + Sync,
    EF: Field + BasedVectorSpace<F>,
>(
    pol_0: &[PF],
    pol_1: &[EFP],
    sum: EF,
) -> DensePolynomial<EF> {
    assert_eq!(DIM, EF::DIMENSION);
    let n = pol_0.len();
    assert_eq!(n, pol_1.len());
    assert!(n.is_power_of_two());
    let half = n / 2;

    type Acc<const D: usize> = ([u128; D], [i128; D]);

    let chunk_size = 1024;

    let (c0_acc, c2_acc) = pol_0[..half]
        .par_chunks(chunk_size)
        .zip(pol_0[half..].par_chunks(chunk_size))
        .zip(
            pol_1[..half]
                .par_chunks(chunk_size)
                .zip(pol_1[half..].par_chunks(chunk_size)),
        )
        .map(|((b_lo, b_hi), (e_lo, e_hi))| {
            let mut c0 = [0u128; DIM];
            let mut c2 = [0i128; DIM];
            for i in 0..b_lo.len() {
                let x0_lanes = b_lo[i].as_slice();
                let x1_lanes = b_hi[i].as_slice();
                let y0_coords = e_lo[i].as_basis_coefficients_slice();
                let y1_coords = e_hi[i].as_basis_coefficients_slice();
                for j in 0..DIM {
                    let y0_j = y0_coords[j].as_slice();
                    let y1_j = y1_coords[j].as_slice();
                    for lane in 0..PF::WIDTH {
                        let x0 = x0_lanes[lane].to_unique_u32() as u64;
                        let y0 = y0_j[lane].to_unique_u32();
                        let y1 = y1_j[lane].to_unique_u32();
                        c0[j] += (y0 as u64 * x0) as u128;
                        c2[j] += (y1 as i64 - y0 as i64) as i128
                            * (x1_lanes[lane].to_unique_u32() as i64 - x0 as i64) as i128;
                    }
                }
            }
            (c0, c2)
        })
        .reduce(
            || ([0u128; DIM], [0i128; DIM]),
            |(mut a0, mut a2): Acc<DIM>, (b0, b2): Acc<DIM>| {
                for j in 0..DIM {
                    a0[j] += b0[j];
                    a2[j] += b2[j];
                }
                (a0, a2)
            },
        );

    let c0 = EF::from_basis_coefficients_fn(|j| F::reduce_product_sum(c0_acc[j]));
    let c2 = EF::from_basis_coefficients_fn(|j| F::reduce_signed_product_sum(c2_acc[j]));
    let c1 = sum - c0.double() - c2;

    DensePolynomial::new(vec![c0, c1, c2])
}

pub fn fold_and_compute_product_sumcheck_polynomial<
    F: PrimeCharacteristicRing + Copy + Send + Sync + 'static,
    EF: Field,
    EFPacking: Algebra<F> + From<EF> + Copy + Send + Sync + 'static,
>(
    pol_0: &[F],         // evals
    pol_1: &[EFPacking], // weights
    prev_folding_factor: EF,
    sum: EF,
    decompose: impl Fn(EFPacking) -> Vec<EF>,
) -> (DensePolynomial<EF>, Vec<Vec<EFPacking>>) {
    let n = pol_0.len();
    assert_eq!(n, pol_1.len());
    assert!(n.is_power_of_two());
    let prev_folding_factor_packed = EFPacking::from(prev_folding_factor);

    let mut pol_0_folded = unsafe { uninitialized_vec::<EFPacking>(n / 2) };
    let mut pol_1_folded = unsafe { uninitialized_vec::<EFPacking>(n / 2) };

    #[allow(clippy::type_complexity)]
    let process_element = |(p0_prev, p0_f): (((&F, &F), (&F, &F)), (&mut EFPacking, &mut EFPacking)),
                           (p1_prev, p1_f): (
        ((&EFPacking, &EFPacking), (&EFPacking, &EFPacking)),
        (&mut EFPacking, &mut EFPacking),
    )| {
        let diff_0 = *p0_prev.1.0 - *p0_prev.0.0;
        let diff_1 = *p0_prev.1.1 - *p0_prev.0.1;
        let x_0 = prev_folding_factor_packed * diff_0 + *p0_prev.0.0;
        let x_1 = prev_folding_factor_packed * diff_1 + *p0_prev.0.1;
        *p0_f.0 = x_0;
        *p0_f.1 = x_1;

        let y_0 = prev_folding_factor_packed * (*p1_prev.1.0 - *p1_prev.0.0) + *p1_prev.0.0;
        let y_1 = prev_folding_factor_packed * (*p1_prev.1.1 - *p1_prev.0.1) + *p1_prev.0.1;
        *p1_f.0 = y_0;
        *p1_f.1 = y_1;

        sumcheck_quadratic(((&x_0, &x_1), (&y_0, &y_1)))
    };

    let (c0_packed, c2_packed) = if n < PARALLEL_THRESHOLD {
        zip_fold_2(pol_0, &mut pol_0_folded)
            .zip(zip_fold_2(pol_1, &mut pol_1_folded))
            .map(|(p0, p1)| process_element(p0, p1))
            .fold((EFPacking::ZERO, EFPacking::ZERO), |(a0, a2), (b0, b2)| {
                (a0 + b0, a2 + b2)
            })
    } else {
        par_zip_fold_2(pol_0, &mut pol_0_folded)
            .zip(par_zip_fold_2(pol_1, &mut pol_1_folded))
            .map(|(p0, p1)| process_element(p0, p1))
            .reduce(
                || (EFPacking::ZERO, EFPacking::ZERO),
                |(a0, a2), (b0, b2)| (a0 + b0, a2 + b2),
            )
    };

    let c0 = decompose(c0_packed).into_iter().sum::<EF>();
    let c2 = decompose(c2_packed).into_iter().sum::<EF>();
    let c1 = sum - c0.double() - c2;

    (DensePolynomial::new(vec![c0, c1, c2]), vec![pol_0_folded, pol_1_folded])
}

#[inline(always)]
pub fn sumcheck_quadratic<F, EF>(((&x_0, &x_1), (&y_0, &y_1)): ((&F, &F), (&EF, &EF))) -> (EF, EF)
where
    F: PrimeCharacteristicRing + Copy,
    EF: Algebra<F> + Copy,
{
    let constant = y_0 * x_0;
    let quadratic = (y_1 - y_0) * (x_1 - x_0);
    (constant, quadratic)
}

/// Product sumcheck polynomial, iterating pairs at an arbitrary bit position
/// in the current layout. Pairs `(i, i | 2^bit)` for `i` with `bit(i)==0`
/// contribute to c0, c2. Pairs with `i >= unpadded_len` are skipped (both
/// `pol_0` entries are known-zero, so they contribute 0 to both c0 and c2).
pub fn compute_product_sumcheck_polynomial_at_bit<
    F: PrimeCharacteristicRing + Copy + Send + Sync,
    EF: Field,
    EFPacking: Algebra<F> + Copy + Send + Sync,
>(
    pol_0: &[F],
    pol_1: &[EFPacking],
    sum: EF,
    bit: usize,
    unpadded_len: usize,
    decompose: impl Fn(EFPacking) -> Vec<EF>,
) -> DensePolynomial<EF> {
    let n = pol_0.len();
    assert_eq!(n, pol_1.len());
    assert!(n.is_power_of_two());
    let stride = 1usize << bit;
    assert!(n >= 2 * stride);
    let lo_mask = stride - 1;
    let new_size = n / 2;

    let compute_at = |new_j: usize| -> (EFPacking, EFPacking) {
        let i_hi = new_j >> bit;
        let i_lo = new_j & lo_mask;
        let i0 = (i_hi << (bit + 1)) | i_lo;
        if i0 >= unpadded_len {
            return (EFPacking::ZERO, EFPacking::ZERO);
        }
        let i1 = i0 | stride;
        sumcheck_quadratic(((&pol_0[i0], &pol_0[i1]), (&pol_1[i0], &pol_1[i1])))
    };

    let (c0_packed, c2_packed) = if new_size < PARALLEL_THRESHOLD {
        (0..new_size)
            .map(compute_at)
            .fold((EFPacking::ZERO, EFPacking::ZERO), |(a0, a2), (b0, b2)| {
                (a0 + b0, a2 + b2)
            })
    } else {
        (0..new_size)
            .into_par_iter()
            .with_min_len(PARALLEL_THRESHOLD)
            .map(compute_at)
            .reduce(
                || (EFPacking::ZERO, EFPacking::ZERO),
                |(a0, a2), (b0, b2)| (a0 + b0, a2 + b2),
            )
    };

    let c0 = decompose(c0_packed).into_iter().sum::<EF>();
    let c2 = decompose(c2_packed).into_iter().sum::<EF>();
    let c1 = sum - c0.double() - c2;

    DensePolynomial::new(vec![c0, c1, c2])
}

/// DIM-templated u128/i128 delayed-modular-reduction variant of
/// `compute_product_sumcheck_polynomial_at_bit`, mirroring
/// `compute_product_sumcheck_polynomial_base_ext_packed` but iterating pairs
/// `(i, i | 2^bit)` for `i` with `bit(i)==0` and skipping pairs where
/// `i >= unpadded_len` (both sides known-zero).
pub fn compute_product_sumcheck_polynomial_base_ext_packed_at_bit<
    const DIM: usize,
    F: PrimeField32,
    PF: PackedField<Scalar = F>,
    EFP: BasedVectorSpace<PF> + Copy + Send + Sync,
    EF: Field + BasedVectorSpace<F>,
>(
    pol_0: &[PF],
    pol_1: &[EFP],
    sum: EF,
    bit: usize,
    unpadded_len: usize,
) -> DensePolynomial<EF> {
    assert_eq!(DIM, EF::DIMENSION);
    let n = pol_0.len();
    assert_eq!(n, pol_1.len());
    assert!(n.is_power_of_two());
    let stride = 1usize << bit;
    assert!(n >= 2 * stride);
    let lo_mask = stride - 1;
    let new_size = n / 2;

    type Acc<const D: usize> = ([u128; D], [i128; D]);
    let chunk_size = 1024;

    let (c0_acc, c2_acc) = (0..new_size)
        .into_par_iter()
        .with_min_len(chunk_size)
        .fold(
            || ([0u128; DIM], [0i128; DIM]),
            |(mut c0, mut c2): Acc<DIM>, new_j| {
                let i_hi = new_j >> bit;
                let i_lo = new_j & lo_mask;
                let i0 = (i_hi << (bit + 1)) | i_lo;
                if i0 >= unpadded_len {
                    return (c0, c2);
                }
                let i1 = i0 | stride;
                let x0_lanes = pol_0[i0].as_slice();
                let x1_lanes = pol_0[i1].as_slice();
                let y0_coords = pol_1[i0].as_basis_coefficients_slice();
                let y1_coords = pol_1[i1].as_basis_coefficients_slice();
                for j in 0..DIM {
                    let y0_j = y0_coords[j].as_slice();
                    let y1_j = y1_coords[j].as_slice();
                    for lane in 0..PF::WIDTH {
                        let x0 = x0_lanes[lane].to_unique_u32() as u64;
                        let y0 = y0_j[lane].to_unique_u32();
                        let y1 = y1_j[lane].to_unique_u32();
                        c0[j] += (y0 as u64 * x0) as u128;
                        c2[j] += (y1 as i64 - y0 as i64) as i128
                            * (x1_lanes[lane].to_unique_u32() as i64 - x0 as i64) as i128;
                    }
                }
                (c0, c2)
            },
        )
        .reduce(
            || ([0u128; DIM], [0i128; DIM]),
            |(mut a0, mut a2): Acc<DIM>, (b0, b2): Acc<DIM>| {
                for j in 0..DIM {
                    a0[j] += b0[j];
                    a2[j] += b2[j];
                }
                (a0, a2)
            },
        );

    let c0 = EF::from_basis_coefficients_fn(|j| F::reduce_product_sum(c0_acc[j]));
    let c2 = EF::from_basis_coefficients_fn(|j| F::reduce_signed_product_sum(c2_acc[j]));
    let c1 = sum - c0.double() - c2;

    DensePolynomial::new(vec![c0, c1, c2])
}

/// Deferred-fold variant: applies the previous round's challenge to
/// `(pol_0, pol_1)` and computes the next round's bare polynomial in a
/// single traversal. The two folds happen at original positions `bit` and
/// `bit + 1` (both LSB-of-the-folded-group, in successive rounds).
///
/// Padding fast path: when both `pol_0` entries of a quadruple are zero
/// (`q00 >= unpadded_len`), skip the `pol_0` fold and the round-2
/// contribution (both are 0). Still folds `pol_1` since weights are
/// non-zero in the padded region and are read/modified by subsequent
/// WHIR rounds.
///
/// Parallelism: we iterate over compact-round-2 indices `new_j ∈ [0, n/4)`
/// element-by-element in parallel. Each `new_j` writes to a unique pair
/// `(p0_lo_idx, p0_hi_idx)` of disjoint slots in the folded buffers; the
/// writes go through raw pointers because chunking into disjoint slices
/// would force a minimum chunk of `2^(bit+1)`, starving cores on later
/// rounds (where `n / 2^(bit+1)` < core count).
pub fn fold_and_compute_product_sumcheck_polynomial_at_bit<
    F: PrimeCharacteristicRing + Copy + Send + Sync + 'static,
    EF: Field,
    EFPacking: Algebra<F> + From<EF> + Copy + Send + Sync + 'static,
>(
    pol_0: &[F],
    pol_1: &[EFPacking],
    prev_folding_factor: EF,
    sum: EF,
    bit: usize,
    unpadded_len: usize,
    decompose: impl Fn(EFPacking) -> Vec<EF>,
) -> (DensePolynomial<EF>, Vec<Vec<EFPacking>>) {
    let n = pol_0.len();
    assert_eq!(n, pol_1.len());
    assert!(n.is_power_of_two());
    let stride_b = 1usize << bit;
    let stride_b1 = stride_b << 1;
    let block = stride_b1 << 1; // 2^(bit+2)
    assert!(n >= block);
    let lo_mask = stride_b - 1;
    let prev_folded_size = n / 2;
    let new_size = n / 4;
    let prev_folding_packed = EFPacking::from(prev_folding_factor);

    let mut pol_0_folded = unsafe { uninitialized_vec::<EFPacking>(prev_folded_size) };
    let mut pol_1_folded = unsafe { uninitialized_vec::<EFPacking>(prev_folded_size) };

    // SAFETY: for `new_j` and `new_j'` both in `[0, n/4)` with `new_j != new_j'`,
    // the slot pairs `(p0_lo_idx, p0_hi_idx)` are distinct — they are a
    // permutation of `[0, n/2)` with each slot hit by exactly one `new_j`
    // (inverse is `new_j = (slot >> (bit+1)) * stride_b | (slot & lo_mask)`
    // regardless of whether `slot` is in the lo or hi half of its block).
    // So the parallel map never writes to the same slot twice, and raw
    // pointer writes across threads are sound.
    let p0f_ptr = pol_0_folded.as_mut_ptr() as usize;
    let p1f_ptr = pol_1_folded.as_mut_ptr() as usize;

    let process = |new_j: usize| -> (EFPacking, EFPacking) {
        let i_hi = new_j >> bit;
        let i_lo = new_j & lo_mask;
        let q00 = (i_hi << (bit + 2)) | i_lo;
        let p0_lo_idx = (i_hi << (bit + 1)) | i_lo;
        let p0_hi_idx = p0_lo_idx | stride_b;

        let q10 = q00 | stride_b;
        let q01 = q00 | stride_b1;
        let q11 = q01 | stride_b;

        let y_0 = prev_folding_packed * (pol_1[q10] - pol_1[q00]) + pol_1[q00];
        let y_1 = prev_folding_packed * (pol_1[q11] - pol_1[q01]) + pol_1[q01];

        let (x_0, x_1, contrib) = if q00 >= unpadded_len {
            (EFPacking::ZERO, EFPacking::ZERO, (EFPacking::ZERO, EFPacking::ZERO))
        } else {
            let x_0 = prev_folding_packed * (pol_0[q10] - pol_0[q00]) + pol_0[q00];
            let x_1 = prev_folding_packed * (pol_0[q11] - pol_0[q01]) + pol_0[q01];
            (x_0, x_1, sumcheck_quadratic(((&x_0, &x_1), (&y_0, &y_1))))
        };

        unsafe {
            let p0f = p0f_ptr as *mut EFPacking;
            let p1f = p1f_ptr as *mut EFPacking;
            *p0f.add(p0_lo_idx) = x_0;
            *p0f.add(p0_hi_idx) = x_1;
            *p1f.add(p0_lo_idx) = y_0;
            *p1f.add(p0_hi_idx) = y_1;
        }

        contrib
    };

    let (c0_packed, c2_packed) = if n < PARALLEL_THRESHOLD {
        (0..new_size).map(process).fold((EFPacking::ZERO, EFPacking::ZERO), |(a0, a2), (b0, b2)| {
            (a0 + b0, a2 + b2)
        })
    } else {
        (0..new_size)
            .into_par_iter()
            .with_min_len(PARALLEL_THRESHOLD)
            .map(process)
            .reduce(
                || (EFPacking::ZERO, EFPacking::ZERO),
                |(a0, a2), (b0, b2)| (a0 + b0, a2 + b2),
            )
    };

    let c0 = decompose(c0_packed).into_iter().sum::<EF>();
    let c2 = decompose(c2_packed).into_iter().sum::<EF>();
    let c1 = sum - c0.double() - c2;

    (DensePolynomial::new(vec![c0, c1, c2]), vec![pol_0_folded, pol_1_folded])
}

/// Run a product sumcheck where every round folds at the SAME bit position
/// of the current layout. Mirrors `run_product_sumcheck` (DIM=5 round-1
/// delayed-reduction path, deferred-fold round-2+ path) plus a padding
/// fast path that skips iterations where both `pol_0` entries are zero.
/// Returns challenges in NATURAL (reversed) order so downstream MLE
/// evaluation sees `folding_randomness[0]` binding the outer-group MSB.
///
/// `unpadded_len` is expressed in the same units as `pol_0.len()` (packed
/// units when `pol_0` is packed).
#[instrument(skip_all)]
pub fn run_product_sumcheck_at_bit<EF: ExtensionField<PF<EF>>>(
    pol_a: &MleRef<'_, EF>,
    pol_b: &MleRef<'_, EF>,
    prover_state: &mut impl FSProver<EF>,
    mut sum: EF,
    n_rounds: usize,
    pow_bits: usize,
    fold_bit: usize,
    unpadded_len: usize,
) -> (MultilinearPoint<EF>, EF, MleOwned<EF>, MleOwned<EF>) {
    assert!(n_rounds >= 1);

    // Round 1: same dispatch as `run_product_sumcheck` — DIM=5 delayed-
    // reduction path for (BasePacked, ExtensionPacked), generic otherwise.
    let first_sumcheck_poly = match (pol_a, pol_b) {
        (MleRef::BasePacked(evals), MleRef::ExtensionPacked(weights)) => {
            if EF::DIMENSION == 5 {
                compute_product_sumcheck_polynomial_base_ext_packed_at_bit::<5, _, _, _, EF>(
                    evals,
                    weights,
                    sum,
                    fold_bit,
                    unpadded_len,
                )
            } else {
                unimplemented!()
            }
        }
        (MleRef::ExtensionPacked(evals), MleRef::ExtensionPacked(weights)) => {
            compute_product_sumcheck_polynomial_at_bit(evals, weights, sum, fold_bit, unpadded_len, |e| {
                EFPacking::<EF>::to_ext_iter([e]).collect()
            })
        }
        (MleRef::Base(evals), MleRef::Extension(weights)) => {
            compute_product_sumcheck_polynomial_at_bit(evals, weights, sum, fold_bit, unpadded_len, |e| vec![e])
        }
        (MleRef::Extension(evals), MleRef::Extension(weights)) => {
            compute_product_sumcheck_polynomial_at_bit(evals, weights, sum, fold_bit, unpadded_len, |e| vec![e])
        }
        _ => unimplemented!(),
    };

    prover_state.add_sumcheck_polynomial(&first_sumcheck_poly.coeffs, None);
    prover_state.pow_grinding(pow_bits);
    let r1: EF = prover_state.sample();
    sum = first_sumcheck_poly.evaluate(r1);
    let mut challenges: Vec<EF> = Vec::with_capacity(n_rounds);
    challenges.push(r1);

    if n_rounds == 1 {
        challenges.reverse();
        return (MultilinearPoint(challenges), sum, pol_a.fold_at_bit(r1, fold_bit), pol_b.fold_at_bit(r1, fold_bit));
    }

    // Round 2: deferred fold of r1 + compute round-2 poly in one traversal.
    let (second_poly, mut folded_a, mut folded_b) = match (pol_a, pol_b) {
        (MleRef::BasePacked(evals), MleRef::ExtensionPacked(weights)) => {
            let (poly, mut both) = fold_and_compute_product_sumcheck_polynomial_at_bit(
                evals,
                weights,
                r1,
                sum,
                fold_bit,
                unpadded_len,
                |e| EFPacking::<EF>::to_ext_iter([e]).collect(),
            );
            let folded_b = both.pop().unwrap();
            let folded_a = both.pop().unwrap();
            (poly, MleOwned::ExtensionPacked(folded_a), MleOwned::ExtensionPacked(folded_b))
        }
        (MleRef::ExtensionPacked(evals), MleRef::ExtensionPacked(weights)) => {
            let (poly, mut both) = fold_and_compute_product_sumcheck_polynomial_at_bit(
                evals,
                weights,
                r1,
                sum,
                fold_bit,
                unpadded_len,
                |e| EFPacking::<EF>::to_ext_iter([e]).collect(),
            );
            let folded_b = both.pop().unwrap();
            let folded_a = both.pop().unwrap();
            (poly, MleOwned::ExtensionPacked(folded_a), MleOwned::ExtensionPacked(folded_b))
        }
        (MleRef::Base(evals), MleRef::Extension(weights)) => {
            let (poly, mut both) = fold_and_compute_product_sumcheck_polynomial_at_bit(
                evals,
                weights,
                r1,
                sum,
                fold_bit,
                unpadded_len,
                |e| vec![e],
            );
            let folded_b = both.pop().unwrap();
            let folded_a = both.pop().unwrap();
            (poly, MleOwned::Extension(folded_a), MleOwned::Extension(folded_b))
        }
        (MleRef::Extension(evals), MleRef::Extension(weights)) => {
            let (poly, mut both) = fold_and_compute_product_sumcheck_polynomial_at_bit(
                evals,
                weights,
                r1,
                sum,
                fold_bit,
                unpadded_len,
                |e| vec![e],
            );
            let folded_b = both.pop().unwrap();
            let folded_a = both.pop().unwrap();
            (poly, MleOwned::Extension(folded_a), MleOwned::Extension(folded_b))
        }
        _ => unimplemented!(),
    };

    prover_state.add_sumcheck_polynomial(&second_poly.coeffs, None);
    prover_state.pow_grinding(pow_bits);
    let r2: EF = prover_state.sample();
    sum = second_poly.evaluate(r2);
    challenges.push(r2);

    // After round 2's deferred fold, `folded_*` holds the round-1 fold
    // (size = original / 2, in pol_0 units). We've conceptually folded with
    // r1 once, so the unpadded suffix has shrunk according to the fold-at-bit
    // formula. r2 hasn't been applied yet.
    let mut cur_size = folded_a.by_ref().packed_len();
    let mut cur_unpadded_len = new_unpadded_suffix_len(unpadded_len, fold_bit, cur_size);

    // Rounds 3..n: each round does a deferred fold of the previous challenge
    // and computes the next round's bare poly in one pass. Dispatch on the
    // current MLE representation (packed vs. unpacked).
    let mut prev_chal = r2;
    for _ in 2..n_rounds {
        let prev_a = std::mem::replace(&mut folded_a, MleOwned::Extension(Vec::new()));
        let prev_b = std::mem::replace(&mut folded_b, MleOwned::Extension(Vec::new()));
        let (poly, new_a, new_b) = match (prev_a, prev_b) {
            (MleOwned::ExtensionPacked(a), MleOwned::ExtensionPacked(b)) => {
                let (poly, mut both) = fold_and_compute_product_sumcheck_polynomial_at_bit(
                    &a,
                    &b,
                    prev_chal,
                    sum,
                    fold_bit,
                    cur_unpadded_len,
                    |e| EFPacking::<EF>::to_ext_iter([e]).collect(),
                );
                let new_b = MleOwned::ExtensionPacked(both.pop().unwrap());
                let new_a = MleOwned::ExtensionPacked(both.pop().unwrap());
                (poly, new_a, new_b)
            }
            (MleOwned::Extension(a), MleOwned::Extension(b)) => {
                let (poly, mut both) = fold_and_compute_product_sumcheck_polynomial_at_bit(
                    &a,
                    &b,
                    prev_chal,
                    sum,
                    fold_bit,
                    cur_unpadded_len,
                    |e| vec![e],
                );
                let new_b = MleOwned::Extension(both.pop().unwrap());
                let new_a = MleOwned::Extension(both.pop().unwrap());
                (poly, new_a, new_b)
            }
            _ => unimplemented!("unexpected MLE variant mid-sumcheck"),
        };
        folded_a = new_a;
        folded_b = new_b;
        cur_size = folded_a.by_ref().packed_len();
        cur_unpadded_len = new_unpadded_suffix_len(cur_unpadded_len, fold_bit, cur_size);

        prover_state.add_sumcheck_polynomial(&poly.coeffs, None);
        prover_state.pow_grinding(pow_bits);
        let r: EF = prover_state.sample();
        sum = poly.evaluate(r);
        challenges.push(r);
        prev_chal = r;
    }

    // Apply the final challenge eagerly (no further compute round).
    let pol_a_owned = folded_a.by_ref().fold_at_bit(prev_chal, fold_bit);
    let pol_b_owned = folded_b.by_ref().fold_at_bit(prev_chal, fold_bit);

    challenges.reverse();
    (MultilinearPoint(challenges), sum, pol_a_owned, pol_b_owned)
}

/// After folding at current-layout bit `fold_bit`, compute the new unpadded
/// suffix length. Same formula as the AIR version in
/// `crates/sub_protocols/src/air_sumcheck.rs`: given the index of the first
/// guaranteed-zero entry in the old (size-2N) array, return the index of the
/// first guaranteed-zero entry in the new (size-N) compact array.
fn new_unpadded_suffix_len(old_len: usize, fold_bit: usize, new_size: usize) -> usize {
    // old_size = 2 * new_size.
    let old_size = new_size * 2;
    if old_len >= old_size {
        return new_size;
    }
    if old_len == 0 {
        return 0;
    }
    let stride = 1usize << fold_bit;
    let block = stride << 1;
    let i_min = if (old_len >> fold_bit) & 1 == 0 {
        old_len
    } else {
        ((old_len >> (fold_bit + 1)) + 1) * block
    };
    if i_min >= old_size {
        return new_size;
    }
    let i_hi = i_min >> (fold_bit + 1);
    let i_lo = i_min & (stride - 1);
    (i_hi << fold_bit) | i_lo
}
